/*+
Simple Java Datalog engine
Author: Werner Stoop
This code is placed in the public domain
Notes, Features and Properties:
  - It can parse and evaluate Datalog programs from files and Strings (actually anything that implements java.io.Reader).
  - It has a fluent API through which it can be embedded in Java applications to run queries.
  - It avoids third party dependencies because it is a proof-of-concept. It should be able to stand alone.
  - It needs negation. I've postponed thinking about it until I'm satisfied with the basic implementation.
    Note that negation is difficult. See for example [ceri] section VI parts B through D.
  - I didn't realize it until I started playing with it that I DO need some built-in predicates to specify certain
    relationships like "not equals". I want to be able to write rules like
        sibling(X, Y) :- parent(Z, X), parent(Z, Y), X <> Y.
    otherwise a person will be his/her own sibling, which may not be what you want.
  - The `parse()` methods should be rethinked (rethought?) to return Expr/Rule objects so that you can have the
		equivalent of JDBC's prepareStatement()
		
2016/04/06 - It now implements "Semi-Naive Bottom-Up" evaluation.
2016/04/08 - I've replaced the code that uses the Streams API with more old-fashioned code. The Streams version
	worked properly, but my rough benchmarks show that the code is ever so slightly more efficient now.
Compile like so:
	> javac JDatalog.java
Run like so:
	> java JDatalog test.dl
References:
  [wiki]  Wikipedia topic, http://en.wikipedia.org/wiki/Datalog
  [elma]  Fundamentals of Database Systems (3rd Edition); Ramez Elmasri, Shamkant Navathe
  [ceri]  What You Always Wanted to Know About Datalog (And Never Dared to Ask); Stefano Ceri, Georg Gottlob, and Letizia Tanca
  [bra1]  Deductive Databases and Logic Programming; Stefan Brass, Univ. Halle, 2009
            http://dbs.informatik.uni-halle.de/Lehre/LP09/c6_botup.pdf
  [meye]  Prolog in Python, Chris Meyers, http://www.openbookproject.net/py4fun/prolog/intro.html
  [banc]  An Amateur’s Introduction to Recursive Query Processing Strategies; Francois Bancilhon, Raghu Ramakrishnan
  [mixu]  mixu/datalog.js; Mikito Takada, https://github.com/mixu/datalog.js
  [kett]  bottom-up-datalog-js; Frederic Kettelhoit http://fkettelhoit.github.io/bottom-up-datalog-js/docs/dl.html
  [davi]  Inference in Datalog; Ernest Davis, http://cs.nyu.edu/faculty/davise/ai/datalog.html
  [gree]  Datalog and Recursive Query Processing; Todd J. Green, Shan Shan Huang, Boon Thau Loo and Wenchao Zhou
            Foundations and Trends in Databases Vol. 5, No. 2 (2012) 105–195, 2013
			http://blogs.evergreen.edu/sosw/files/2014/04/Green-Vol5-DBS-017.pdf
  [bra2]  Bottom-Up Query Evaluation in Extended Deductive Databases, Stefan Brass, 1996
			https://www.deutsche-digitale-bibliothek.de/binary/4ENXEC32EMXHKP7IRB6OKPBWSGJV5JMJ/full/1.pdf
  [sund]  Datalog Evaluation Algorithms, Dr. Raj Sunderraman, 1998
			http://tinman.cs.gsu.edu/~raj/8710/f98/alg.html
  [ull1]  Lecture notes: Datalog Rules Programs Negation; Jeffrey D. Ullman;
			http://infolab.stanford.edu/~ullman/cs345notes/cs345-1.ppt
  [ull2]  Lecture notes: Datalog Logical Rules Recursion; Jeffrey D. Ullman;
			http://infolab.stanford.edu/~ullman/dscb/pslides/dlog.ppt
Bottom-up is also called forward chaining in some of the documents; likewise, top-down is also called backward chaining. [davi]
says explains that using top-down might lead to infinite loops, but says that it is sufficient to prevent this by failing the test
if you encounter a goal that you've already encountered in the stack.
Section VI-A of [ceri] talks about built-in predicates. They also use syntax like `sibling(X, Y) :- parent(Z, X), parent(Z, Y), X != Y.`
as I've suggested above, but a take away is that it can also be written as `sibling(X, Y) :- parent(Z, X), parent(Z, Y), notequals(X, Y).`
and then `notequals()` be treated specially. It seems to me that you can override the Expr.unify() method in a subclass.
Bear in mind:
  - The built-in predicates should be evaluated last, ie. `X != Y, parent(Z, X), parent(Z, Y).` should be evaluated as if it was written as
    `parent(Z, X), parent(Z, Y), X != Y.` with the X != Y last.
	  - You can probably rearrange the predicates in Rule's constructor without losing anything.
      - [ceri] says that exceptions can (or should) be made for an equals() predicate, but I'm not sure what they mean.
      - Arithmetic predicates, such as plus(X,Y,Z) => X + Y = Z aren't that simple. They should be evaluated as soon as the input variables
	    (X and Y) in this case becomes available, so that Z can be computed for the remaining goals.
  - Actually, if the predicate is special, you don't need to do the stream().flatMap() over all the facts, since at that stage you're only
    interested in the values in the `bindings`, and there's no need to iterate over all the facts.
  - The overrided unify() method bla bla
For the fluent API, I can use a static method like this `Expr.notequals("X", "Y")`. Is it a good idea?
I recently rediscovered [elma] on my bookshelf from my university days. My copy is an older edition of the book, but it has a very thorough
explaination in chapter 25.
It is connceptually possible to make the `List<String> terms` a List<Object> instead, so that you can store complex Java objects in the 
database. The `isVariable()` method will just have to be modified to check whether its parameter is instanceof String and starts with
an uppercase character, the bindings will become a StackMap<String, Object>, the result of `query()` will be a List<Map<String, Object>>
and a couple of toString methods will have to be modified. It won't be that useful a feature if you just use the parser, but it could be 
a nice to have if you use the API. I don't intend to implement it at the moment, though.
*/

import java.util.Arrays;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.Collection;
import java.util.Collections;
import java.util.stream.Stream;


import java.util.stream.Collectors;
import java.util.regex.Pattern;

import java.io.StreamTokenizer;
import java.io.StringReader;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.IOException;
import java.io.Reader;
import java.io.FileReader;
import java.io.FileWriter;

class JDatalog {

	private Collection<Expr> edb;
	private Collection<Rule> idb;
    
	private static boolean debugEnable = false;

	public JDatalog() {
		this.edb = new ArrayList<Expr>();
		this.idb = new ArrayList<Rule>();
	}

	static class Expr {

		String predicate;
		List<String> terms;
		double exrpprob;
		Expr(String predicate, List<String> terms) {
			this.predicate = predicate;
			this.terms = terms;
		}
		Expr(double prob,String predicate, String ... terms) {
			this.exrpprob=prob;
			this.predicate = predicate;
			this.terms = new ArrayList<String>();
			for(String ti : terms) {
				this.terms.add(ti);
			}
		}

		Expr(String predicate, String... terms) {
			this(predicate, Arrays.asList(terms));
		}

		int arity() {
			return terms.size();
		}

		public boolean isGround() {
			for(String term : terms) {
				if(isVariable(term))
					return false;
			}
			return true;
		}
		private static Expr parse(StreamTokenizer scan) throws DatalogException {
			Profiler.Timer timer = Profiler.getTimer("parseExpr");
			try {
				scan.nextToken();
				if(scan.ttype != StreamTokenizer.TT_WORD) {
					throw new DatalogException("[line " + scan.lineno() + "] Predicate expected");
				}
				String pred = scan.sval;
				if(scan.nextToken() != '(') {
					throw new DatalogException("[line " + scan.lineno() + "] Expected '(' after predicate");
				}
				List<String> terms = new ArrayList<String>();
				if(scan.nextToken() != ')') {
					scan.pushBack();
					do {
						if(scan.nextToken() == StreamTokenizer.TT_WORD)	{
							terms.add(scan.sval);
						} else if(scan.ttype == '"' || scan.ttype == '\'') {
							terms.add(scan.sval);
						} else if(scan.ttype == StreamTokenizer.TT_NUMBER) {
							// Remove trailing zeros; http://stackoverflow.com/a/14126736/115589
							String value;
							if(scan.nval == (long) scan.nval)
								value = String.format("%d",(long)scan.nval);
							else
								value = String.format("%s",scan.nval);
							terms.add(value);
						} else {
							throw new DatalogException("[line " + scan.lineno() + "] Expected term in expression");
						}
					} while(scan.nextToken() == ',');
					if(scan.ttype != ')') {
						throw new DatalogException("[line " + scan.lineno() + "] Expected ')'");
					}
				}
				return new Expr(pred, terms);
			} catch (IOException e) {
				throw new DatalogException(e);
			} finally {
				timer.stop();
			}
		}

		boolean unify(Expr that, Map<String, String> bindings) {
			if(!this.predicate.equals(that.predicate) || this.arity() != that.arity()) {
				return false;
			}
			for(int i = 0; i < this.arity(); i++) {
				String term1 = this.terms.get(i);
				String term2 = that.terms.get(i);
				if(isVariable(term1)) {
					if(!term1.equals(term2)) {
						if(!bindings.containsKey(term1)) {
							bindings.put(term1, term2);
						} else if (!bindings.get(term1).equals(term2)) {
							return false;
						}
					}
				} else if(isVariable(term2)) {
					if(!bindings.containsKey(term2)) {
						bindings.put(term2, term1);
					} else if (!bindings.get(term2).equals(term1)) {
						return false;
					}
				} else if (!term1.equals(term2)) {
					return false;
				}
			}
			return true;
		}
		boolean unify(Expr that, StackMap<String, String> bindings) {
			if(!this.predicate.equals(that.predicate) || this.arity() != that.arity()) {
				return false;
			}
			for(int i = 0; i < this.arity(); i++) {
				String term1 = this.terms.get(i);
				String term2 = that.terms.get(i);
				if(isVariable(term1)) {
					if(!term1.equals(term2)) {
						if(!bindings.containsKey(term1)) {
							bindings.put(term1, term2);
						} else if (!bindings.get(term1).equals(term2)) {
							return false;
						}
					}
				} else if(isVariable(term2)) {
					if(!bindings.containsKey(term2)) {
						bindings.put(term2, term1);
					} else if (!bindings.get(term2).equals(term1)) {
						return false;
					}
				} else if (!term1.equals(term2)) {
					return false;
				}
			}
			return true;
		}
		Expr substitute(StackMap<String, String> bindings) {
			// that.terms.add() below doesn't work without the new ArrayList()
			Expr that = new Expr(this.predicate, new ArrayList<String>());
			for(String term : this.terms) {
				String value;
				if(isVariable(term)) {
					value = bindings.get(term);
					if(value == null) {
						value = term;
					}
				} else {
					value = term;
				}
				that.terms.add(value);
			}
			return that;
		}

		Expr substitute2(Map<String, String> bindings,Expr fact,List<Expr> Matchedgoals,Rule rule,Set<Expr> facts) {
			Expr that = new Expr(this.predicate,new ArrayList<String>());
			for(String term : this.terms)
			{
				String value;
				if(isVariable(term)) 
				{
					value = bindings.get(term);
					if(value == null)
					{
						value = term; // would this matter??
					}
				}
				else 
				{
					value = term;
				} 
				that.terms.add(value);
				
			}
			if(bindings.size()==fact.arity())
			{
			that.exrpprob=fact.exrpprob*rule.ruleprob;
			}
			else
				
			{
				
				double[] minarray=new double[Matchedgoals.size()];
				for(int i=0;i<Matchedgoals.size();i++)
				{
					minarray[i]=Matchedgoals.get(i).exrpprob;
				}
				double minvalue=conjunctionfunction(minarray);
				that.exrpprob=propogationfunction(minvalue, rule.ruleprob);
//				for(Expr exfacts:facts)
//				{
//					if(exfacts.equals(that))
//					{
//						that.exrpprob=exfacts.exrpprob+that.exrpprob-(exfacts.exrpprob*that.exrpprob);
//					}
//				}	
			}
			return that;
		}
		double propogationfunction(double value,double rulevalue)
		{
			return value*rulevalue;
		}
		double conjunctionfunction(double[] minarray)
		{
			double min=minarray[0];
			for(int i=0;i<minarray.length;i++)
			{
				if(minarray[i]<min)
					min=minarray[i];
			}
			return min;
		}
		@Override
		public boolean equals(Object other) {
			if(other == null || !(other instanceof Expr)) {
				return false;
			}
			Expr that = ((Expr) other);
			if(!this.predicate.equals(that.predicate)) {
				return false;
			}
			if(arity() != that.arity()) {
				return false;
			}
			for(int i = 0; i < terms.size(); i++) {
				if(!terms.get(i).equals(that.terms.get(i))) {
					return false;
				}
			}
			return true;
		}

		@Override
		public int hashCode() {
			int hash = predicate.hashCode();
			for(String term : terms) {
				hash += term.hashCode();
			}
			return hash;
		}

		// Regex for terms that contain non-alphanumeric charaters and should be quoted in toString()
		static final Pattern quotedTerm = Pattern.compile("[^a-zA-Z0-9._]");

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append(predicate).append('(');
			for(int i = 0; i < terms.size(); i++) {
				sb.append(terms.get(i));
				if(i < terms.size() - 1)
					sb.append(", ");
			}
			sb.append(')');
			
			if(this.exrpprob==0.0)
			{
				
			}
			else
			{
				sb.append(':');
			sb.append(this.exrpprob);
			}
			return sb.toString();
		}
	}
	static class Rule {

		Expr head;
		List<Expr> body;
		double ruleprob;
		Rule(Expr head, List<Expr> body) {
			this.head = head;
			this.body = body;
		}

		Rule(Expr head, Expr... body) {
			this(head, Arrays.asList(body));
		}
		Rule(double prob,Expr head, List<Expr> body) {
			this.head = head;
			this.body = body;
			this.ruleprob=prob;
		}
		Rule(double prob,Expr head, Expr... body) {
			this.ruleprob=prob;
			this.head = head;
			this.body = new LinkedList<Expr>();
			for(Expr e : body) {
				this.body.add(e);
			}
		}
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append(head);
			sb.append(" :- ");
			for(int i = 0; i < body.size(); i++) {
				sb.append(body.get(i));
				if(i < body.size() - 1)
					sb.append(", ");
			}
			sb.append(':');
			sb.append(this.ruleprob);
			return sb.toString();
		}
		// Enforce the rule that variables on the LHS must appear on the RHS
		boolean validate() {
			Set<String> variables = new HashSet<String>();
			for(String term : head.terms) {
				if(isVariable(term)) {
					variables.add(term);
				}
			}
			for(Expr expr : body) {
				for(String term : expr.terms) {
					if(isVariable(term)) {
						variables.remove(term);
					}
				}
			}
			return variables.isEmpty();
		}

		
	}

	private static boolean isVariable(String term) {
		return Character.isUpperCase(term.charAt(0));
	}

	public JDatalog rule(Expr head, Expr... body) throws DatalogException {
		Rule rule = new Rule(head, body);
		if(!rule.validate()) {
			throw new DatalogException("Rule is invalid: " + rule);
		}
		idb.add(rule);
		return this;
	}

	public JDatalog fact(String predicate, String... terms) throws DatalogException {
		Expr expr = expr(predicate, terms);
		if(!expr.isGround()) {
			throw new DatalogException("Facts must be ground: " + expr);
		}
		edb.add(expr);
		return this;
	}

	// Intended for import static
	public static Expr expr(String predicate, String... terms) {
		return new Expr(predicate, terms);
	}

	/* If you're executing a file that may contain multiple queries, you can pass
	#execute(Reader, QueryOutput) a QueryOutput object that will be used to display
	all the results from the separate queries, with their goals.
	Otherwise #execute(Reader, QueryOutput) will just return the answers from the
	last query. */
	public static interface QueryOutput {
		public void writeResult(List<Expr> goals, List<Map<String, String>> answers);
	}

	/* Default implementation of QueryOutput */
	public static class StandardQueryOutput implements QueryOutput {
		@Override
		public void writeResult(List<Expr> goals, List<Map<String, String>> answers) {
			Profiler.Timer timer = Profiler.getTimer("output");
			try {
				//System.out.println(JDatalog.toString(goals) + "?");
				if(!answers.isEmpty()){
					if(answers.get(0).isEmpty()) {
						System.out.println("  Yes.");
					} else {
						for(Map<String, String> answer : answers) {
							System.out.println("  " + JDatalog.toString(answer));
						}
					}
				} else {
					System.out.println("  No.");
				}
			} finally {
				timer.stop();
			}
		}
	}

	/* Executes all the statements in a file/string/whatever the Reader is wrapping */
	public List<Map<String, String>> execute(Reader reader, QueryOutput output) throws DatalogException, ParseException {
		Profiler.Timer timer = Profiler.getTimer("execute");
		try {
			debug("Executing reader...");

			StreamTokenizer scan = new StreamTokenizer(reader);
			scan.ordinaryChar('.'); // '.' looks like a number to StreamTokenizer by default
			scan.commentChar('%'); // Prolog-style % comments; slashSlashComments and slashStarComments can stay as well.
			scan.quoteChar('"');
			scan.quoteChar('\'');
			//scan.parseNumbers(); // WTF? You can't disable parsing of numbers unless you reset the syntax (http://stackoverflow.com/q/8856750/115589)
			scan.nextToken();

			// Tracks the last query's answers
			List<Map<String, String>> answers = null;

			// Tracks the last query's goals (for output purposes)
			List<Expr> goals = new ArrayList<Expr>();

			while(scan.ttype != StreamTokenizer.TT_EOF) {
				scan.pushBack();
				answers = parseStmt(scan, goals);
				if(answers != null && output != null) {
					output.writeResult(goals, answers);
				}
				scan.nextToken();
			}
			return answers;
		} catch (IOException e) {
			throw new DatalogException(e);
		} finally {
			timer.stop();
		}
	}

	private List<Map<String, String>> parseStmt(StreamTokenizer scan, List<Expr> goals) throws DatalogException, ParseException {
		Profiler.Timer timer = Profiler.getTimer("parseStmt");
		try {

			scan.nextToken();
			// "delete a(b,X)." deletes facts from the IDB that matches the query.
			// It is not standard Datalog AFAIK.
			if(scan.ttype == StreamTokenizer.TT_WORD && scan.sval.equalsIgnoreCase("delete")) {
				goals.clear();
				do {
					Expr e = Expr.parse(scan);
					goals.add(e);
				} while(scan.nextToken() == ',');
				if(scan.ttype != '.') {
					throw new DatalogException("[line " + scan.lineno() + "] Expected '.' after 'delete'");
				}
				if(debugEnable) {
					System.out.println("Parser [line " + scan.lineno() + "]: Deleting goals: " + toString(goals));
				}
				delete(goals);
				return null;
			} else {
				scan.pushBack();
			}

			Expr head = Expr.parse(scan);
			//System.out.println(scan.nval+"headaftwe");
			scan.nextToken();
			//System.out.println(scan.nval+"head2");
			 if(scan.ttype=='?')
			 {				
					// It's a query
					List<Expr> query = new ArrayList<Expr>();
					query.add(head);
					if (scan.ttype != '.' && scan.ttype != '?' && scan.ttype != ',') {
						throw new ParseException("'.', ',' or '?' expected after fact/query expression");
					}					
					while(scan.ttype == ',') {
						query.add(Expr.parse(scan));
						scan.nextToken();
					}			
					//.out.println("Parser: got query: " + toString(query));
						
					if(scan.ttype == '?') {
						
						return query(query);
					} else {
						throw new ParseException("'?' expected after query");
					}
			}
			if(scan.ttype== ':')
			{
				double exprob=0.0;
				if(scan.nextToken() == '-')
				{
					//.out.println("inside if");
				// We're dealing with a rule
//				if(scan.nextToken() != '-') {
//					throw new ParseException("':-' expected");
//				}				
				List<Expr> body = new ArrayList<Expr>();
				do {
					Expr arg = Expr.parse(scan);
					body.add(arg);
				} while(scan.nextToken() == ',');
				
				if(scan.ttype==':')
				{
					scan.nextToken();
					exprob=scan.nval;
				}
				scan.nextToken();
				if(scan.ttype != '.') {
					throw new ParseException("'.' expected after rule");
				}
				Rule rule = new Rule(exprob,head, body);
				if(!rule.validate()) {
					throw new ParseException("Rule is invalid: " + rule);
				}
				//.out.println("Parser: got rule: " + rule);
				idb.add(rule);
				}
			 else {
				// We're dealing with a fact, or a query
				//.out.println("inside else");
				//.out.println(scan.nval+"value");
				head.exrpprob=scan.nval;
					//.out.println("fact");
					// It's a fact
					//.out.println(head.terms);
					if(!head.isGround())
					{
						throw new ParseException("Fact is not grounded (it can't contain variables): " + head);
					}
					//.out.println("Parser: got fact: " + head);
					edb.add(head);
					scan.nextToken();
					if(scan.ttype!='.')
					{
						throw new ParseException("Fact should end with a dot: " + head);
					}
				}
			}	
		} catch (IOException e) {
			throw new DatalogException(e);
		} finally {
			timer.stop();
		}
		return null;
	}
	static class ParseException extends Exception {
		public ParseException(String message) {
			super(message);
		}
		public ParseException(Exception cause) {
			super(cause);
		}
	}
	
	static class DatalogException extends Exception {
		public DatalogException(String message) {
			super(message);
		}
		public DatalogException(Exception cause) {
			super(cause);
		}
	}
   
	public List<Map<String, String>> query(String statement) throws DatalogException, ParseException {
		// It would've been fun to wrap the results in a java.sql.ResultSet, but damn,
		// those are a lot of methods to implement:
		// https://docs.oracle.com/javase/8/docs/api/java/sql/ResultSet.html
		StringReader reader = new StringReader(statement);
		return execute(reader, null);
	}

	public List<Map<String, String>> query(Expr... goals) throws IOException {
		return query(Arrays.asList(goals));
	}

	public List<Map<String, String>> query(List<Expr> goals) throws IOException {
		FileWriter fw=new FileWriter("C:\\Users\\syeda\\Desktop\\naive semi\\DATALOG\\output.txt");
		PrintWriter pw=new PrintWriter(fw);
		Profiler.Timer timer = Profiler.getTimer("query");
		try {
			if(goals.isEmpty())
				return new ArrayList<Map<String, String>>();

			// getRelevantRules() strips a large part of the rules, so if I want to
			// do some benchmarking of buildDatabase(), I use the IDB directly instead:
			// Collection<Rule> rules = idb;
			Collection<Rule> rules = getRelevantRules(goals);
			if(debugEnable) {
				//.out.println("To answer query, we need to evaluate: " + toString(rules));
			}

			// Build the database. A Set ensures that the facts are unique
			Collection<Expr> dataset = buildDatabase(new HashSet<Expr>(edb), rules);
			if(debugEnable) {
				//.out.println("query(): Database = " + toString(dataset));
			}
			ArrayList<Expr> al=new ArrayList<Expr>(dataset);
			for(int i=0;i<dataset.size();i++)
			{
//				pw.write(database.get(i).predicate);
//				pw.write("(");
//				for(int j=0;j<database.get(i).arity();j++)
//				{
//					pw.write(database.get(i).terms.get(j));
//					pw.write(",");
//				}
//				pw.write("):");
//				String s=
				pw.write(al.get(i).toString());
				pw.println();
			    
			}
			pw.close();
			fw.close();
			return matchAnswers(dataset, goals);
		} finally {
			timer.stop();
		}
	}

	/* Returns a list of rules that are relevant to the query.
		If for example you're quering employment status, you don't care about family relationships, etc.
		The advantages of this of this optimization becomes bigger the complexer the rules get. */
	private Collection<Rule> getRelevantRules(List<Expr> originalGoals) {
		Profiler.Timer timer = Profiler.getTimer("getRelevantRules");
		try {
			Collection<Rule> relevant = new HashSet<Rule>();
			LinkedList<Expr> goals = new LinkedList<Expr>(originalGoals);
			while(!goals.isEmpty()) {
				Expr expr = goals.poll();
				for(Rule rule : idb) {
					if(rule.head.predicate.equals(expr.predicate) && !relevant.contains(rule)) {
						relevant.add(rule);
						goals.addAll(rule.body);
					}
				}
			}
			return relevant;
		} finally {
			timer.stop();
		}
	}

	/* Basically, this constructs the dependency graph for semi-naive evaluation: In the returned map, the string
		is a predicate in the rules' heads that maps to a collection of all the rules that have that predicate in
		their body so that we can easily find the rules that are affected when new facts are deduced in different
		iterations of buildDatabase().
		For example if you have a rule p(X) :- q(X) then there will be a mapping from "q" to that rule
		so that when new facts q(Z) are deduced, the rule will be run in the next iteration to deduce p(Z) */
	private Map<String, Collection<Rule>> buildDependantRules(Collection<Rule> allRules) {
		Profiler.Timer timer = Profiler.getTimer("buildDependantRules");
		try {
			Map<String, Collection<Rule>> map = new HashMap<String, Collection<Rule>>();
			for(Rule rule : allRules) {
				for(Expr goal : rule.body) {
					Collection<Rule> rules = map.get(goal.predicate);
					if(rules == null) {
						rules = new ArrayList<Rule>();
						map.put(goal.predicate, rules);
					}
					if(!rules.contains(rule))
						rules.add(rule);
				}
			}
			return map;
		} finally {
			timer.stop();
		}
	}

	private Collection<Rule> getDependantRules(Collection<Expr> facts, Map<String, Collection<Rule>> dependants) {
		Profiler.Timer timer = Profiler.getTimer("getDependantRules");
		try {			
			Set<Rule> dependantRules = new HashSet<Rule>();
			for(Expr fact : facts) {
				Collection<Rule> rules = dependants.get(fact.predicate);
				if(rules != null) {
					dependantRules.addAll(rules);
				}
			}
			return dependantRules;			
		} finally {
			timer.stop();
		}
	}

	private Collection<Expr> buildDatabase(Set<Expr> facts, Collection<Rule> allRules)
	{
		int iteration=0;
		Profiler.Timer timer = Profiler.getTimer("buildDatabase");
		Long startTime = System.currentTimeMillis();
		
		try {
			
			Collection<Rule> rules = allRules;
			Set<Expr> edges=new HashSet<Expr>(facts);
			Set<Expr> factssend=new HashSet<Expr>(edges);
			Map<String, Collection<Rule>> dependants = buildDependantRules(allRules);

			while(true) 
			{
				Profiler.Timer loopTimer = Profiler.getTimer("loopTimer");
				try 
				{
					
					// Match each rule to the facts
					Profiler.Timer matchRuleTimer = Profiler.getTimer("matchRules");
					Set<Expr> newFacts = new HashSet<Expr>();
					//Set<Expr> newnodups= new HashSet<Expr>();
					HashMap<Expr,ArrayList<Double>> dup=new HashMap<Expr,ArrayList<Double>>();
					for(Rule rule : rules)
					{
						List<Expr> results = matchRule(factssend,rule);
						for(int i=0;i<results.size();i++)
				        {
							//newnodups.add(results.get(i));
							if(dup.containsKey(results.get(i)))
							{
								dup.get(results.get(i)).add(results.get(i).exrpprob);
							}
							else
							{
								ArrayList<Double> prob=new ArrayList<Double>();
								prob.add(results.get(i).exrpprob);
								dup.put(results.get(i),prob);
							}
				        }
				
					}
					
					Set<Expr> newnodups=dup.keySet();
					
					matchRuleTimer.stop();
					
					for(Expr nf:newnodups)
					{
						for(Expr of:facts)
						{
							if(nf.equals(of))
							{
								dup.get(nf).add(of.exrpprob);
							}
						}
						
					}
					for(Expr e1:dup.keySet())
					{
						if(dup.get(e1).size()>1)
						{
							Double probnew=disjunctionfunction(dup.get(e1));
							//Double probnew=max(dup.get(e1));
							e1.exrpprob=probnew;
							if(newFacts.contains(e1))
							{
								newFacts.remove(e1);
							}
							newFacts.add(e1);
						}
						else
						{
							if(newFacts.contains(e1))
							{
								newFacts.remove(e1);
							}
							newFacts.add(e1);
						}
					}
					
					// Delta facts: The new facts that have been added in this iteration
					// for semi-naive evaluation.
					
					Profiler.Timer deltaFactsTimer = Profiler.getTimer("deltaFacts");
					Set<Expr> tempnew = new HashSet<Expr>(newFacts);
					for(Expr nf1:tempnew)
					{
						for(Expr of1:facts)
						{
							if(nf1.equals(of1))
							{
								double a1=Math.abs(nf1.exrpprob-of1.exrpprob);
								if(a1<0.001)
								{
									newFacts.remove(of1);
								}
								
							}
						}
					}
					deltaFactsTimer.stop();
					
					// Repeat until there are no more facts added
					if(newFacts.isEmpty())
					{
						System.out.println("I-"+ ++iteration);
						long endTime = System.currentTimeMillis();
						long runTime = endTime - startTime;
						System.out.println("Runtime for pattern in milliseconds: " + runTime);
//						System.out.println("Size:"+facts.size());
						//.out.println("Size:"+facts.size());
						return facts;
					}
					if(debugEnable) 
					{
						//.out.println("buildDatabase(): deltaFacts = " + toString(newFacts));
					}

					rules = getDependantRules(newFacts, dependants);

					Profiler.Timer addAllTimer = Profiler.getTimer("addAll");
					Set<Expr> temp = new HashSet<Expr>(facts);
					for(Expr nf1:newFacts)
					{
						for(Expr of1:temp)
						{
							if(nf1.equals(of1))
							{
								facts.remove(of1);
							     facts.add(nf1);
							}
							else
							{
								facts.add(nf1);
							}
						}
					}
					
					factssend.clear();
					factssend.addAll(edges);
					factssend.addAll(newFacts);
					addAllTimer.stop();
//					System.out.println("facts"+facts);
//					System.out.println("newFacts"+newFacts);
//					System.out.println("HashMap"+dup);
					iteration++;
				} 
				finally 
				{
					
					loopTimer.stop();
				}
				//System.out.println("I-"+iteration);
			}
			
		}
		finally 
		{
			
			timer.stop();
		}
	}
	Double max(ArrayList<Double> al)
	{
		Double max1=0.0;
		for(int i=0;i<al.size();i++)
		{
			if(al.get(i)>max1)
			{
				max1=al.get(i);
			}
		}
		return max1;
	}
	Double disjunctionfunction(ArrayList<Double> al)
	{
		double sum=0;
		double mul=1;
		for(int i=0;i<al.size();i++)
		{
			sum=sum+al.get(i);
			mul=mul*al.get(i);
		}
//		double max=0;
//		for(int i=0;i<al.size();i++)
//		{
//			if(al.get(i)>max)
//				max=al.get(i);
//		}
//		return max;
		return sum-mul;
	}
	private List<Expr> matchRule2(final Set<Expr> facts, Rule rule) {
		Profiler.Timer timer = Profiler.getTimer("matchRule");
		try {
			List<Expr> results = new LinkedList<Expr>();
			if(rule.body.isEmpty()) // If this happens, you're using the API wrong.
				return results;
			// Match the rule body to the facts.
			// For each match found, substitute the bindings into the head to create a new fact.
			Collection<StackMap<String, String>> answers =  matchGoals2(rule.body, facts, null);
			for(StackMap<String, String> answer : answers) {
				results.add(rule.head.substitute(answer));
			}
			return results;
		} finally {
			timer.stop();
		}
	}
	List<Expr> matchRule(final Set<Expr> facts, Rule rule) {		

		//.out.println("matchRule(): " + rule + "; " );
		
		List<Expr> goals = rule.body;
					
		List<Expr> results = new LinkedList<Expr>();	
		List<Expr> matchedGoals = new LinkedList<Expr>();
		
		matchGoals(facts, goals, null, rule, results,matchedGoals);		
		
		//.out.println("Results: ");
		//printFacts(results);
		
		
		return results;
	}
	void matchGoals(final Set<Expr> facts, List<Expr> goals, Map<String, String> bindings, Rule rule, List<Expr> results,List<Expr> matchedGoals)
	{
		if(goals.isEmpty())
			return;
		
		Expr goal = goals.get(0);
		goals = goals.subList(1, goals.size());
		
		
		for(Expr fact : facts)
		{		
			////.out.println("  - Comparing goal " + goal + " against fact " + fact);
			Map<String, String> newBindings = new StackMap2<String, String>(bindings);
			if(fact.unify(goal, newBindings))
			{
				matchedGoals.add(fact);
				if(goals.isEmpty()) 
				{
					Expr subs =rule.head.substitute2(newBindings,fact,matchedGoals,rule,facts);
					//.out.println("* Inserting fact " + subs);
					results.add(subs);
					matchedGoals.remove(fact);
				} else 
				{
					matchGoals(facts, goals, newBindings, rule, results,matchedGoals);
				}
			}
			matchedGoals.remove(fact);
		}
	}
	private Collection<StackMap<String, String>> matchGoals2(List<Expr> goals, final Collection<Expr> facts, StackMap<String, String> bindings) {
		// First goal
		Expr goal = goals.get(0); // Assumes goals won't be empty
		
		boolean lastGoal = (goals.size() == 1);
		
		// Match each fact to the first goal.
		// If the fact matches: If it is the last/only goal then we can return the bindings
		// as an answer, otherwise we recursively check the remaining goals.
		Collection<StackMap<String, String>> answers = new ArrayList<StackMap<String, String>>();
		for(Expr fact : facts) {
			if(!fact.predicate.equals(goal.predicate)) {
				continue;
			}
			StackMap<String, String> newBindings = new StackMap<String, String>(bindings);
			if(fact.unify(goal, newBindings)) {
				if(lastGoal) {
					answers.add(newBindings);
				} else {
					// More goals to match. Recurse with the remaining goals.
					answers.addAll(matchGoals2(goals.subList(1, goals.size()), facts, newBindings));
				}
			}
		}
		
		return answers;
	}

	private List<Map<String, String>> matchAnswers(Collection<Expr> database, List<Expr> goals) {
		Profiler.Timer timer = Profiler.getTimer("matchAnswers");
		try {
			Collection<StackMap<String, String>> results = matchGoals2(goals, database, null);
			List<Map<String, String>> answers = new ArrayList<Map<String, String>>(results.size());
			for(StackMap<String, String> result : results) {
				answers.add(result.flatten());
			}	
			return answers;
		} finally {
			timer.stop();
		}
	}

	public boolean delete(Expr... facts) throws IOException {
		return delete(Arrays.asList(facts));
	}

	/* Queries a set of goals and deletes all the facts that matches the query */
	public boolean delete(List<Expr> goals) throws IOException {
		Profiler.Timer timer = Profiler.getTimer("delete");
		try {
			List<Map<String, String>> answers = query(goals);
			List<Expr> facts = answers.stream()
				// Create a new StackMap from the Map in the answer (StackMap doesn't implement Map anymore)
				.map(StackMap::new)
				// and substitute that map on each goal
				.flatMap(answer -> goals.stream().map(goal -> goal.substitute(answer)))
				.collect(Collectors.toList());
			if(debugEnable) {
				//.out.println("Facts to delete: " + toString(facts));
			}
			return edb.removeAll(facts);
		} finally {
			timer.stop();
		}
	}

	static void debug(String message) {
		// I'm not happy with this. Remove later.
		if(debugEnable) {
			//.out.println(message);
		}
	}

	static String toString(Collection<?> collection) {
		StringBuilder sb = new StringBuilder("[");
		for(Object o : collection)
			sb.append(o.toString()).append(". ");
		sb.append("]");
		return sb.toString();
	}

	static String toString(Map<String, String> bindings) {
		StringBuilder sb = new StringBuilder("{");
		int s = bindings.size(), i = 0;
		for(String k : bindings.keySet()) {
			String v = bindings.get(k);
			sb.append(k).append(": ");
			if(Expr.quotedTerm.matcher(v).find()) {
				// Needs more org.apache.commons.lang3.StringEscapeUtils#escapeJava(String)
				sb.append('"').append(v.replaceAll("\"", "\\\\\"")).append("\"");
			} else {
				sb.append(v);
			}
			if(++i < s) sb.append(", ");
		}
		sb.append("}");
		return sb.toString();
	}

	// If you want to do profiling, run the file several times to get finer grained results.
	// private static final int NUM_RUNS = 1000;
	private static final int NUM_RUNS = 1;

	public static void startup_seminaive(String... args)  {

		try {
		if(args.length > 0) {
			try {
				// Read input from a file...
				QueryOutput qo = new StandardQueryOutput();
				for(int run = 0; run < NUM_RUNS; run++) {

					JDatalog jDatalog = new JDatalog();

					for(String arg : args) {
						debug("Executing file " + arg);
						try( Reader reader = new BufferedReader(new FileReader("C:\\Users\\syeda\\Desktop\\naive semi\\DATALOG\\input.txt")) ) {
							jDatalog.execute(reader, qo);
						}
					}
				}

				if(NUM_RUNS > 1) {
					//.out.println("Profile for running " + toString(Arrays.asList(args)) + "; NUM_RUNS=" + NUM_RUNS);
					Profiler.keySet().stream().sorted().forEach(key -> {
						double time = Profiler.average(key);
						double total = Profiler.total(key);
						int count = Profiler.count(key);
						//.out.println(String.format("%-20s time: %10.4fms; total: %12.2fms; count: %d", key, time, total, count));
					});
				}

			} catch (DatalogException | IOException e) {
				e.printStackTrace();
			}
		} else {
			// Get input from command line
			JDatalog jDatalog = new JDatalog();
			BufferedReader buffer = new BufferedReader(new InputStreamReader(System.in));
			//.out.println("JDatalog: Java Datalog engine\nInteractive mode; type 'exit' to quit.");
			while(true) {
				try {
					//.out.print("> ");
					String line = buffer.readLine();
					if(line == null) {
						break; // EOF
					}
					line = line.trim();
					if(line.equalsIgnoreCase("exit")) {
						break;
					}

					List<Map<String, String>> answers = jDatalog.query(line);

					// If answers is null, the line passed to `jDatalog.query(line)` was a fact or a rule, not a query.
					// If answers is empty, then it was a query that doesn't have any answers, so the output is "No."
					// If the answers are empty maps, then it was the type of query that only wanted a yes/no answer, like
					//     `siblings(alice,bob)?` and the answer is "Yes."
					// Otherwise the answers is a list of all bindings that satisfies the query.
					if(answers != null) {
						if(!answers.isEmpty()){
							if(answers.get(0).isEmpty()) {
								System.out.println("Yes.");
							} else {
								for(Map<String, String> answer : answers) {
									System.out.println(JDatalog.toString(answer));
								}
							}
						} else {
							System.out.println("No.");
						}
					}

				} catch (DatalogException | IOException e) {
					e.printStackTrace();
				}
			}
		}
		}
		catch( ParseException e)
		{
			
		}
		/* //This is how you would use the fluent API:
		try {
			JDatalog jDatalog = new JDatalog();
			jDatalog.fact("parent", "a", "aa")
				.fact("parent", "a", "ab")
				.fact("parent", "aa", "aaa")
				.fact("parent", "aa", "aab")
				.fact("parent", "aaa", "aaaa")
				.fact("parent", "c", "ca");
			jDatalog.rule(expr("ancestor", "X", "Y"), expr("parent", "X", "Z"), expr("ancestor", "Z", "Y"))
				.rule(expr("ancestor", "X", "Y"), expr("parent", "X", "Y"))
				.rule(expr("sibling", "X", "Y"), expr("parent", "Z", "X"), expr("parent", "Z", "Y"))
				.rule(expr("related", "X", "Y"), expr("ancestor", "Z", "X"), expr("ancestor", "Z", "Y"));
			List<Map<String, String>> answers = jDatalog.query(expr("ancestor", "aa", "X"));
			answers.stream().forEach(answer -> System.out.println(" -> " + toString(answer)));
			System.out.println("Before Deletion: " + toString(jDatalog.edb));
			jDatalog.delete(expr("parent", "aa", "X"), expr("parent", "X", "aaaa")); // deletes parent(aa,aaa) and parent(aaa,aaaa)
			System.out.println("After Deletion: " + toString(jDatalog.edb));
			answers = jDatalog.query(expr("ancestor", "aa", "X"));
			answers.stream().forEach(answer -> System.out.println(" -> " + toString(answer)));
		} catch (DatalogException e) {
			e.printStackTrace();
		} */


		/* // The JDatalog.execute(String) method runs queries directly.
		try{
			QueryOutput qo = new StandardQueryOutput();
			JDatalog jDatalog = new JDatalog();
			jDatalog.execute("foo(bar). foo(baz).", qo);
			jDatalog.execute("foo(What)?", qo);
		} catch (DatalogException e) {
			e.printStackTrace();
		} */

	}

	/* Map that has a parent Map where it looks up a value if the value is not in the current one.
		It actually only needs containsKey(), put() and get(). It originally implemented the Map<>
		interface, but there were practical considerations, so it doesn't anymore.
	*/
	static class StackMap<K,V> {
		private Map<K,V> self;
		private StackMap<K,V> parent;

		public StackMap() {
			self = new HashMap<K, V>();
			this.parent = null;
		}

		public StackMap(StackMap<K,V> parent) {
			self = new HashMap<K, V>();
			this.parent = parent;
		}

		// There's a difference with the other constructor, beware
		public StackMap(Map<K,V> map) {
			self = new HashMap<K, V>(map);
			this.parent = null;
		}

		Map<K,V> flatten() {
			Map<K,V> map;
			if(parent != null)
				map = parent.flatten();
			else
				map = new HashMap<K, V>();
			map.putAll(self);
			return map;
		}

		public V put(K key, V value) {
			return self.put(key, value);
		}

		public boolean containsKey(K key) {
			if(self.containsKey(key))
				return true;
			if(parent != null)
				return parent.containsKey(key);
			return false;
		}

		public V get(K key) {
			V value = self.get(key);
			if(value != null)
				return value;
			if(parent != null)
				return parent.get(key);
			return null;
		}
	}
	static class StackMap2<K,V> implements Map<K,V> {
		private Map<K,V> self;
		private Map<K,V> parent;
		
		public StackMap2() {
			self = new HashMap<K, V>();
			this.parent = null;
		}
		
		public StackMap2(Map<K,V> parent) {
			self = new HashMap<K, V>();
			this.parent = parent;
		}
		
		Map<K,V> flatten() {
			Map<K,V> map = new HashMap<K,V>();
			map.putAll(this); // HashMap uses entrySet() in putAll()
			return map;
		}
		
		public V put(K key, V value) {
			return self.put(key, value);
		}
		
		public boolean containsKey(Object key) {
			if(self.containsKey(key))
				return true;
			else if(parent != null)
				return parent.containsKey(key);
			else 
				return false;
		}
		
		public V get(Object key) {
			V value = self.get(key);
			if(value != null)
				return value;
			else if(parent != null)
				return parent.get(key);
			else 
				return null;
		}

		public Set<Map.Entry<K,V>> entrySet() {
			Set<Map.Entry<K,V>> entries = new HashSet<Map.Entry<K,V>>();
			if(parent != null) 
				entries.addAll(parent.entrySet());
			entries.addAll(self.entrySet());
			return entries;
		}
		public int size() {
			int s = self.size();
			if(parent != null)
				s += parent.size();
			return s;
		}
		
		public void clear() {
			throw new UnsupportedOperationException();
		}
		
		public boolean equals(Object o) {
			throw new UnsupportedOperationException();
		}
		public int hashCode() {
			throw new UnsupportedOperationException();
		}
		public Set<K> keySet() {
			throw new UnsupportedOperationException();
		}
		public void putAll(Map<? extends K,? extends V> m) {
			throw new UnsupportedOperationException();
		}
		public V remove(Object key) {
			throw new UnsupportedOperationException();
		}
		public Collection<V> values() {
			throw new UnsupportedOperationException();
		}		
		public boolean containsValue(Object value) {
			throw new UnsupportedOperationException();
		}		
		public boolean isEmpty() {
			throw new UnsupportedOperationException();
		}		
	}
	/* Profiling class.
	I had to write my own because I didn't want to pull in any external dependencies.
	`buckets` maps the name of a bucket to a List of elapsed times so that you can have
	multiple timers under different names.
	*/
	static class Profiler {

		// FYI: Java 8 actually has Instant and Duration classes.
		// Not sure whether they're really useful here, though.

		static class Timer {
			private long start;
			private List<Long> bucket;

			Timer(List<Long> bucket) {
				start = System.currentTimeMillis();
				this.bucket = bucket;
			}

			long stop() {
				long elapsed = (System.currentTimeMillis() - start);
				bucket.add(elapsed);
				return elapsed;
			}
		}

		private Map<String, List<Long>> buckets;

		private static Profiler instance;

		private Profiler() {
			buckets = new ConcurrentHashMap<String, List<Long>>();
		}

		public static Profiler getInstance() {
			if(instance == null) {
				instance = new Profiler();
			}
			return instance;
		}

		public static Timer getTimer(String name) {
			List<Long> bucket = getInstance().getBucket(name);
			return new Timer(bucket);
		}

		List<Long> getBucket(String name) {
			if(!buckets.containsKey(name)) {
				List<Long> list = Collections.synchronizedList(new ArrayList<Long>(NUM_RUNS));
				buckets.putIfAbsent(name, list);
			}
			return buckets.get(name);
		}

		public static double average(String name) {
			List<Long> times = getInstance().getBucket(name);
			if(times.size() == 0) {
				return 0;
			}
			synchronized(times) {
				long sum = 0;
				for(Long time : times) {
					sum += time;
				}
				return (double)sum / times.size();
			}
		}

		public static long total(String name) {
			List<Long> times = getInstance().getBucket(name);
			long sum = 0;
			synchronized(times) {
				for(Long time : times) {
					sum += time;
				}
			}
			return sum;
		}

		public static int count(String name) {
			return getInstance().getBucket(name).size();
		}

		public static double stdDev(String name) {
			// I'm sure I'm going to be really embarrased when I figure out
			// why the stdDev looks so strange...
			List<Long> times = getInstance().getBucket(name);
			synchronized(times) {
				double avg = average(name);
				double sumSq = 0.0;
				for(Long time : times) {
					sumSq += (time - avg) * (time - avg);
				}
				double variance = sumSq / times.size();
				return Math.sqrt(variance);
			}
		}

		public static Set<String> keySet() {
			return getInstance().buckets.keySet();
		}
	}
}