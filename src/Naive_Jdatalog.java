/*
Simple Java Datalog engine 
Author: Werner Stoop
2016/03/23 - This one is "Naive Bottom-Up"; I intend to make it more sophisticated eventually.
Compile like so:
	> javac JDatalog.java
Run like so:
	> java JDatalog test.dl
References
  [wiki]  Wikipedia topic, http://en.wikipedia.org/wiki/Datalog
  [ceri]  What You Always Wanted to Know About Datalog (And Never Dared to Ask); Stefano Ceri, Georg Gottlob, and Letizia Tanca
  [bras]  Deductive Databases and Logic Programming; Stefan Brass, Univ. Halle, 2009
  [meye]  Prolog in Python, Chris Meyers, http://www.openbookproject.net/py4fun/prolog/intro.html
  [banc]  An Amateur’s Introduction to Recursive Query Processing Strategies; Francots Banctlhon, Raghu Ramakrrshnan
  [mixu]  mixu/datalog.js; Mikito Takada, https://github.com/mixu/datalog.js
  [kett]  bottom-up-datalog-js; Frederic Kettelhoit http://fkettelhoit.github.io/bottom-up-datalog-js/docs/dl.html 
  [davi]  Inference in Datalog; Ernest Davis, http://cs.nyu.edu/faculty/davise/ai/datalog.html
  
Bottom-up is also called forward chaining in some of the documents; likewise, top-down is also called backward chaining.
[davi] says explains that using top-down might lead to infinite loops, but says that it is sufficient to prevent this by
failing the test if you encounter a goal that you've already encountered in the stack.
*/

import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.Deque;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.stream.Collectors;


import java.util.Optional;

import java.io.StreamTokenizer;
import java.io.StringReader;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.IOException;
import java.io.Reader;
import java.io.FileReader;
import java.io.FileWriter;


class Naive_Jdatalog {

	private List<Expr> edb;
	private List<Rule> idb;
	static int iteration=0;
	private static boolean debugEnable = false;
	
	public Naive_Jdatalog() {
		this.edb = new LinkedList<Expr>();
		this.idb = new LinkedList<Rule>();
	}

	static class Expr implements Comparable<Expr> {
	
		String predicate;
		List<String> terms;
		double exrpprob;
		Expr(String predicate) {
			this.predicate = predicate;
			this.terms = new ArrayList<String>();
		}
		
		Expr(String predicate, String ... terms) {
			this.predicate = predicate;
			this.terms = new ArrayList<String>();
			for(String ti : terms) {
				this.terms.add(ti);
			}
		}
		Expr(double prob,String predicate, String ... terms) {
			this.exrpprob=prob;
			this.predicate = predicate;
			this.terms = new ArrayList<String>();
			for(String ti : terms) {
				this.terms.add(ti);
			}
		}
		
		Expr(String predicate, List<String> terms) {
			this.predicate = predicate;
			this.terms = terms;
		}
		
		int arity() {return terms.size();}
		
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
		
		public boolean isGround() {
			for(String term : terms) {
				if(isVariable(term))
					return false;
			}
			return true;
		}
		
		boolean unify(Expr that, Map<String, String> bindings) {
			// System.out.print("     Unifying " + this + " against " + that + "; bindings: " + toString(bindings));
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
		Expr substitute2(Map<String, String> bindings) {
			Expr that = new Expr(this.predicate);
			for(String term : this.terms) {
				String value;
				if(isVariable(term)) {
					value = bindings.get(term);
					if(value == null) {
						value = term; // would this matter??
					}
				} else {
					value = term;
				} 
				that.terms.add(value);
			}
			return that;
		}
		Expr substitute(Map<String, String> bindings,Expr fact,List<Expr> Matchedgoals,Rule rule,Set<Expr> facts) {
			Expr that = new Expr(this.predicate);
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
		
		static Expr parse(StreamTokenizer scan) throws ParseException {
			try {
				scan.ordinaryChar('_');
				scan.nextToken();
			//	System.out.println(StreamTokenizer.TT_WORD);
				if(scan.ttype != StreamTokenizer.TT_WORD)
				{
					throw new ParseException("predicate expected");
				}
					String pred = scan.sval;
				//System.out.println(pred);
				if(scan.nextToken() != '(')
					throw new ParseException("'(' expected");

				List<String> terms = new ArrayList<String>();
				if(scan.nextToken() != ')') {
					
					scan.pushBack();
				do {
					//	System.out.println("yolo");
						int se=scan.nextToken();
//						if(se != StreamTokenizer.TT_WORD && se != StreamTokenizer.TT_NUMBER)
//							throw new ParseException("term expected");
						if(se==StreamTokenizer.TT_WORD)
						{
						terms.add(scan.sval);
						}
						else if(se==StreamTokenizer.TT_NUMBER)
						{
							String n1=Integer.toString((int)(scan.nval));
							terms.add(n1);
						}
						else
						{	throw new ParseException("term expected");
					
						}
					}while(scan.nextToken() == ',');
					if(scan.ttype != ')')
					{
						throw new ParseException("')' expected");
					}				
				}
				//System.out.println(" after if");
				return new Expr(pred, terms);				
			} catch (IOException e) {
				throw new ParseException(e);
			}
		}
		
		public boolean equals(Object other) {
			if(other == null || !(other instanceof Expr))
				return false;			
			Expr that = ((Expr) other);
			if(!this.predicate.equals(that.predicate))
				return false;
			if(arity() != that.arity())
				return false;			
			for(int i = 0; i < terms.size(); i++) {
				if(!terms.get(i).equals(that.terms.get(i)))
					return false;
			}
			return true;
		}
		
		public int hashCode() {
			int hash = predicate.hashCode();
			for(String term : terms) {
				hash += term.hashCode();
			}
			return hash;
		}
		
		// To be able to sort answers
		public int compareTo(Expr thatObject) {
			Expr that = (Expr)thatObject;
			int r = this.predicate.compareTo(that.predicate);
			if(r == 0) {
				for(int i = 0; i < Math.min(this.arity(), that.arity()); i++) {
					r = this.terms.get(i).compareTo(that.terms.get(i));
					if(r != 0)
						return r;
				}				
				if(this.arity() != that.arity()) {
					// You're not supposed to get into this situation
					return that.arity() - this.arity();
				}
			} else {
				return r;
			}
			return 0;
		}
	}

	static class Rule {
	
		Expr head;
		List<Expr> body;
		double ruleprob;
		Rule(Expr head, Expr... body) {
			this.head = head;
			this.body = new ArrayList<Expr>();
			for(Expr e : body) {
				this.body.add(e);
			}
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
	
	public Naive_Jdatalog add(Rule rule) {
		idb.add(rule);
		return this;
	}
	//reachable(X,Y) :- edge(X,Y):0.5.
	//reachable(X,Y) :- edge(X,Z), reachable(Z,Y):0.5.
	//sameclique(X,Y) :- reachable(X,Y), reachable(Y,X):0.5.
	//edge(0, 1):0.5.
	public Naive_Jdatalog add(Expr fact) {
		edb.add(fact);
		return this;
	}
	
	List<Map<String, String>> execute(Reader reader) throws ParseException {
		try {
			//System.out.println("Executing reader...");
			StreamTokenizer scan = new StreamTokenizer(reader);
			
			scan.ordinaryChar('.'); // looks like a number	
			
			scan.nextToken();
			List<Map<String, String>> answers = null;
			while(scan.ttype != StreamTokenizer.TT_EOF) {
				scan.pushBack();
				answers = parseLine(scan);
				if(answers != null) {
					if(!answers.isEmpty()){					
						if(answers.get(0).isEmpty()) {
							System.out.println("Yes.");
						} else {
							for(Map<String, String> answer : answers) {
								System.out.println(" " + toString(answer));
							}
						}
					} else {
						System.out.println("No.");
					}
				}
				scan.nextToken();
			}			
			return answers;
		} catch (IOException e) {
			throw new ParseException(e);
		}
	}
				
	private List<Map<String, String>> parseLine(StreamTokenizer scan) throws ParseException {
		try {
			Expr head = Expr.parse(scan);
		//	System.out.println(scan.nval+"headaftwe");
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
			//		System.out.println("Parser: got query: " + toString(query));
						
					if(scan.ttype == '?') {
						
						return answerQuery(query);
					} else {
						throw new ParseException("'?' expected after query");
					}
			}
			if(scan.ttype== ':')
			{
				double exprob=0.0;
				if(scan.nextToken() == '-')
				{
				//	System.out.println("inside if");
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
				//System.out.println("Parser: got rule: " + rule);
				idb.add(rule);
				}
			 else {
				// We're dealing with a fact, or a query
				//System.out.println("inside else");
				//System.out.println(scan.nval+"value");
				head.exrpprob=scan.nval;
					//System.out.println("fact");
					// It's a fact
					//System.out.println(head.terms);
					if(!head.isGround())
					{
						throw new ParseException("Fact is not grounded (it can't contain variables): " + head);
					}
					//System.out.println("Parser: got fact: " + head);
					edb.add(head);
					scan.nextToken();
					if(scan.ttype!='.')
					{
						throw new ParseException("Fact should end with a dot: " + head);
					}
				}
			}				
		} catch (IOException e) {
			throw new ParseException(e);
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
	
	List<Map<String, String>> answerQuery(Expr... query) throws IOException {		
		List<Expr> goals = new LinkedList<Expr>();
		for(Expr goal : query) {
			goals.add(goal);
		}
		return answerQuery(goals);
	}
	List<Map<String, String>> answerQuery(List<Expr> query) throws IOException {
		FileWriter fw=new FileWriter("C:\\Users\\syeda\\Desktop\\naive semi\\DATALOG\\output.txt");
		PrintWriter pw=new PrintWriter(fw);
		Long startTime = System.currentTimeMillis();
		Set<Expr> dataset = buildDatabase(new HashSet<Expr>(edb), idb);
		
		List<Expr> database = new ArrayList<Expr>(dataset);
		for(int i=0;i<database.size();i++)
		{
//			pw.write(database.get(i).predicate);
//			pw.write("(");
//			for(int j=0;j<database.get(i).arity();j++)
//			{
//				pw.write(database.get(i).terms.get(j));
//				pw.write(",");
//			}
//			pw.write("):");
//			String s=
			pw.write(database.get(i).toString());
			pw.println();
		    
		}
		
		debug("answerQuery(): Database:\n" + toString(database));
		long endTime = System.currentTimeMillis();
		long runTime = endTime - startTime;
		System.out.println("Runtime for pattern in milliseconds: " + runTime);
		pw.close();
		fw.close();
		return evalQuery(database, query);
	}
	
Set<Expr> buildDatabase(Set<Expr> facts, List<Rule> rules) {
		
		
	//	System.out.println("buildDatabase(); facts.size()=" + facts.size());
		Set<Expr> newFacts = new HashSet<Expr>(facts);
		HashMap<Expr,ArrayList<Double>> dup=new HashMap<Expr,ArrayList<Double>>();
		ArrayList<Expr> dupkeys=new ArrayList<Expr>();
		for(Rule rule : rules)
		{
			List<Expr> results = matchRule(facts, rule);
			for(int i=0;i<results.size();i++)
		        {
					
					dupkeys.add(results.get(i));
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
		//System.out.println(newFacts);
		//System.out.println(dup.size());
		//System.out.println(dup);
//		newFacts.addAll(dup.keySet());
		
		//System.out.println("buildDatabase(); facts.size()=" + facts.size() + "; newFacts.size()=" + newFacts.size());
		if(facts.size() == newFacts.size()) 
		{
			if(probabilitymatch(facts,newFacts))
			{
				
			System.out.println(++iteration);
			return newFacts;
			}
			else
			{
				++iteration;
				return buildDatabase(newFacts, rules);
			}
		} else
		{
			++iteration;
			return buildDatabase(newFacts, rules);
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
	boolean probabilitymatch(Set<Expr> facts,Set<Expr> newfacts)
	{
		for(Expr e1:newfacts)
		{
			for(Expr e2:facts)
			{
				if(e1.equals(e2))
				{
					double a1=Math.abs(e1.exrpprob-e2.exrpprob);
					
					if(a1>0.001)
					{
						return false;
					}
				}
			}
		}
		return true;
	}
	
	Double disjunctionfunction(ArrayList<Double> al)
	{
//		double sum=0;
//		double mul=1;
//		for(int i=0;i<al.size();i++)
//		{
//			sum=sum+al.get(i);
//			mul=mul*al.get(i);
//		}
		double max=0;
		for(int i=0;i<al.size();i++)
		{
			if(al.get(i)>max)
				max=al.get(i);
		}
		return max;
		
	}
	
	List<Expr> matchRule(final Set<Expr> facts, Rule rule) {		

		//System.out.println("matchRule(): " + rule + "; " );
		
		List<Expr> goals = rule.body;
					
		List<Expr> results = new LinkedList<Expr>();	
		List<Expr> matchedGoals = new LinkedList<Expr>();
		matchGoals(facts, goals, null, rule, results,matchedGoals);		
		
		//System.out.println("Results: ");
		//printFacts(results);
		
		
		return results;
	}
	
	private void matchGoals2(final Collection<Expr> facts, List<Expr> goals, Map<String, String> bindings, Expr head, List<Expr> results, List<Map<String, String>> answers) {
		if(goals.isEmpty())
			return;
		
		Expr goal = goals.get(0);
		goals = goals.subList(1, goals.size());
		
		for(Expr fact : facts) {		
			debug("  - Comparing goal " + goal + " against fact " + fact);
			StackMap<String, String> newBindings = new StackMap<String, String>(bindings);
			if(fact.unify(goal, newBindings)) {
				if(goals.isEmpty()) {
					// Use `head` and `results` for derived facts when building the database
					if(head != null && results != null) {
						Expr subs = head.substitute2(newBindings);
						debug("    * Inserting fact " + subs);
						results.add(subs);
					}
					// Use `answers` to store the bindings when answering queries
					if(answers != null) {
						debug("    * Inserting answer");
						answers.add(newBindings.flatten());
					}
				} else {
					matchGoals2(facts, goals, newBindings, head, results, answers);
				}
			}
		}
	}
	
	void matchGoals(final Set<Expr> facts, List<Expr> goals, Map<String, String> bindings, Rule rule, List<Expr> results,List<Expr> matchedGoals)
	{
		if(goals.isEmpty())
			return;
		
		Expr goal = goals.get(0);
		goals = goals.subList(1, goals.size());
		
		
		for(Expr fact : facts)
		{		
			//System.out.println("  - Comparing goal " + goal + " against fact " + fact);
			Map<String, String> newBindings = new StackMap<String, String>(bindings);
			if(fact.unify(goal, newBindings))
			{
				matchedGoals.add(fact);
				if(goals.isEmpty()) 
				{
					Expr subs =rule.head.substitute(newBindings,fact,matchedGoals,rule,facts);
			//		System.out.println("* Inserting fact " + subs);
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
	private List<Map<String, String>> evalQuery(List<Expr> database, List<Expr> goals) {
		List<Map<String, String>> answers = new LinkedList<Map<String, String>>();
		matchGoals2(database, goals, null, null, null, answers);
		return answers;
	}	
	
	static void debug(String message) {
		if(debugEnable) {
			System.out.println(message);
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
		for(String k : bindings.keySet()) {
			sb.append(k).append(": ").append(bindings.get(k)).append(", ");
		}
		sb.append("}");
		return sb.toString();
	}
		
	public static void startup_naive(String[] args) {
		
		Naive_Jdatalog jDatalog = new Naive_Jdatalog();
		try {
			if(args.length > 0) {
				//System.out.println("Parsing " + args[0]);
				try( Reader reader = new BufferedReader(new FileReader("C:\\Users\\syeda\\Desktop\\naive semi\\DATALOG\\input.txt")) ) {
					jDatalog.execute(reader);
					
				}
			} else {
				System.out.println("No command-line parameters supplied; using System.in");
				try( Reader reader = new BufferedReader(new InputStreamReader(System.in)) ) {
					
					jDatalog.execute(reader);
				}
			}
		} catch (ParseException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		/* //This is how you would use the fluent API:
		JDatalog jDatalog = new JDatalog();
		
		jDatalog.add(new Expr("parent", "a", "aa"));
		jDatalog.add(new Expr("parent", "a", "ab"));
		jDatalog.add(new Expr("parent", "aa", "aaa"));
		jDatalog.add(new Expr("parent", "aa", "aab"));
		jDatalog.add(new Expr("parent", "aaa", "aaaa"));
		jDatalog.add(new Expr("parent", "c", "ca"));
		
		jDatalog.add(new Rule(new Expr("ancestor", "X", "Y"), new Expr("parent", "X", "Z"), new Expr("ancestor", "Z", "Y")));
		jDatalog.add(new Rule(new Expr("ancestor", "X", "Y"), new Expr("parent", "X", "Y")));		
		
		List<Map<String, String>> answers = jDatalog.answerQuery(new Expr("ancestor", "aa", "X")); */
	}
	
	/* Map that has a parent Map where it looks up a value if the value is not in the current one.
		It actually only needs containsKey(), put() and get() so I've replaced the implementations of
		the other methods to throw UnsupportedOperationException
		I suppose it isn't strictly necessary that it implements the Map<> interface, but here we are.
	*/
	static class StackMap<K,V> implements Map<K,V> {
		private Map<K,V> self;
		private Map<K,V> parent;
		
		public StackMap() {
			self = new HashMap<K, V>();
			this.parent = null;
		}
		
		public StackMap(Map<K,V> parent) {
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
}
