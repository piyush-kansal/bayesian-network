import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.InvalidPropertiesFormatException;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;

import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.InputStreamReader;

class BayesNetData
{
	class Node
	{
		final public Map<Map<String,Boolean>, Float> probs = new HashMap<Map<String,Boolean>, Float>();
		final public Set<String> suc = new TreeSet<String>();
		final public Set<String> pre = new TreeSet<String>();
	}
	
	final Map<String, Node> _graph = new HashMap<String, Node>();
	
	private static String NameNormalize(Object o)
	{
		return o.toString().trim().toLowerCase();
	}
	
	private void _loadGraph(InputStream is_graph) throws InvalidPropertiesFormatException, IOException
	{
		final Properties graph = new Properties();
		graph.loadFromXML(is_graph);
		
		for(Map.Entry<Object, Object> item:graph.entrySet())
		{
			final String key = NameNormalize(item.getKey());
			final Set<String> suc;
			
			if(_graph.containsKey(key))
				suc = _graph.get(key).suc;
			else
			{
				final Node node = new Node();
				suc = node.suc;
				_graph.put(key, node);
			}
			
			final String[] values = item.getValue().toString().split(",");
			for(String node:values)
			{
				String tempSuc = NameNormalize(node);

				if(!node.isEmpty())
				{
					final Set<String> tempPred;
					suc.add(tempSuc);

					if(_graph.containsKey(tempSuc))
						tempPred = _graph.get(tempSuc).pre;
					else
					{
						final Node temp = new Node();
						tempPred = temp.pre;
						_graph.put(tempSuc, temp);
					}

					tempPred.add(key);
				}	
			}
		}		
	}
	
	private void _loadProbs(InputStream is_probs) throws InvalidPropertiesFormatException, IOException
	{
		final Properties probs = new Properties();
		probs.loadFromXML(is_probs);
		for(Map.Entry<Object, Object> item:probs.entrySet())
		{
			final String key = NameNormalize(item.getKey().toString());
			final String[] parts = key.split("\\|");
			final Node node = _graph.get(NameNormalize(parts[0]));
			if(node!=null)	// just skip absent nodes
				node.probs.put(createProbKey(parts.length>1?parts[1]:""), Float.valueOf(item.getValue().toString()));
		}
	}
	
	public BayesNetData(InputStream is_graph, InputStream is_probs) throws InvalidPropertiesFormatException, IOException
	{
		_loadGraph(is_graph);
		_loadProbs(is_probs);
	}
	
	public Set<String> getNodes()
	{
		// re: actually, we don't need to sort set of nodes. it makes simpler to read.
		return Collections.unmodifiableSet(new TreeSet<String>(_graph.keySet()));
	}
	
	public Set<String> getSuc(String snode)
	{
		final Node node = _graph.get(NameNormalize(snode));
		return node==null?null:Collections.unmodifiableSet(node.suc);
	}

	public Set<String> getPre(String snode)
	{
		final Node node = _graph.get(NameNormalize(snode));
		return node==null?null:Collections.unmodifiableSet(node.pre);
	}

	public Map<String, Boolean> createProbKey(String s)
	{
		return createProbKey(s.split(","));
	}
	
	public Map<String, Boolean> createProbKey(String... skeys)
	{
		final Map<String, Boolean> pkey = new HashMap<String, Boolean>();
		
		for(String key: skeys)
		{
			boolean value = true;
			String nkey = NameNormalize(key);

			if(nkey.startsWith("~"))
			{
				value = false;
				nkey = NameNormalize(nkey.substring(1));
			}

			if(_graph.containsKey(nkey))
				pkey.put(nkey, value);
		}
		
		return pkey;
	}

	public Map<Map<String,Boolean>, Float> getProbabilityTable(String snode)
	{
		final Node node = _graph.get(NameNormalize(snode));
		return Collections.unmodifiableMap(node.probs);	
	}
	
	public float getProbability(String node, String cond)
	{
		final Map<Map<String,Boolean>, Float> map = getProbabilityTable(node);

		if(map==null)
			return 0;

		final Float v = map.get(createProbKey(cond));
		return v==null?0:v;
	}

	public float getProb(String node, String cond) {
		if(cond.isEmpty())
			return infer(node);

		String nStr = node+","+cond;
		float dVal = infer(cond);

		if(dVal != 0)
			return infer(nStr)/dVal;
		else
			return 0;
	}

	public float infer(String stat) {
		float prob = 0;
		boolean notPresent;
		final String[] statVar = stat.split(",");
		String tempVar, statNotPresent = "";

		for(String curNode:getNodes()) {
			notPresent = true;

			for(String curVar:statVar) {
				tempVar = "";

				if(curVar.equals("~"+curNode) || curVar.equals(curNode)) {
					if(notPresent == false) {
						if(!curVar.equals(tempVar))
							return 0;
					}
					else {
						notPresent = false;
						tempVar = curVar;
					}
				}
			}

			if(notPresent == true) {
				if(statNotPresent.isEmpty())
					statNotPresent+=curNode;
				else
					statNotPresent+=","+curNode;
			}
		}

		final String[] notPresentVars = statNotPresent.split(",");

		ArrayList<String> statExt = new ArrayList<String>();
		statExt.add(stat);

		if(notPresentVars.length>1) {
			for(String np:notPresentVars) {
				int size = statExt.size();

				while(size>0) {
					String tmp = statExt.get(0);
					statExt.remove(tmp);
					statExt.add(tmp+","+np);
					statExt.add(tmp+",~"+np);
					size--;
				}
			}
		}

		for(String temp:statExt)
			prob += inferForNPVars(temp);

		return prob;
	}

	public float inferForNPVars(String stat) {
		boolean curVarVal;
		float prob = 1;
		final String[] statVar = stat.split(",");
		String tempCond;

		for(String curVar:statVar) {
			curVarVal = true;
			Set <String> pre;

			if(curVar.charAt(0) == '~') {
				curVarVal = false;
				curVar = curVar.substring(1);
				pre = getPre(curVar);
			}
			else
				pre = getPre(curVar);

			tempCond = "";
			
			if(!pre.isEmpty()) {
				for(String curPre:pre) {
					if(stat.contains("~"+curPre)) {
						if(!tempCond.isEmpty())
							tempCond += ",~"+curPre;
						else
							tempCond += "~"+curPre;
					}
					else {
						if(!tempCond.isEmpty()) 
							tempCond += ","+curPre;
						else
							tempCond += curPre;
					}	
				}
			}

			float curProb = getProbability(curVar, tempCond);
			if(!curVarVal)
				curProb = 1 - curProb;

			prob *= curProb;
		}

		return prob;
	}
}

public class BayesNetLoad
{
	public static void PrintGraph(BayesNetData bn)
	{
		for(String node: bn.getNodes())
		{
			System.out.println(node+"(S) -> "+bn.getSuc(node));
			System.out.println(node+"(P) -> "+bn.getPre(node));
		}
	}
	
	public static void PrintProbs(BayesNetData bn)
	{
		for(String node: bn.getNodes())
			System.out.println(node+" -> "+bn.getProbabilityTable(node));
	}
	
	public static void main(String[] args) throws IOException
	{	
		String node = "", cond = "";
		final BayesNetData bn = new BayesNetData(new FileInputStream("TD1_graph.xml"), new FileInputStream("TD1_probs.xml"));
		BufferedReader ip = new BufferedReader(new InputStreamReader(System.in));

		System.out.println("****** Printing Graph ******");
		PrintGraph(bn);
		System.out.println("*************************");
		System.out.println("\n");
		System.out.println("****** Printing Probability Tables ******");
		PrintProbs(bn);
		System.out.println("**********************************");
		System.out.println("\n");
			
		System.out.println("****** Take I/P from User ******");
		System.out.println("Enter node:");
		node = ip.readLine();
		System.out.println("Enter cond:");
		cond = ip.readLine();
		System.out.println("**********************************");
		System.out.println("\n");

		if(node.isEmpty())
		{
			System.out.println("Invalid i/p in node. Exiting ...");
			System.exit(1);
		}

		System.out.println("P("+node+"|"+cond+") = "+bn.getProb(node, cond));
	}
}