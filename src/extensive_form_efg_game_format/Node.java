package extensive_form_efg_game_format;

import java.util.ArrayList;

public class Node {

	private String mNodeName;
	private int mInfoSetNum;
	private String mInfoSetName;
	private ArrayList<String> mListOfActions;
	private ArrayList<Double> mListOfProbabilities;
	private int mOutcome;
	private String mOutcomeName;
	private ArrayList<Double> mListOfPayoffs;
	private int mPlayerNum;

	public Node(String name, int infoset, ArrayList<String> actions, ArrayList<Double> probabilities, int outcome) {

		mNodeName = name;
		mInfoSetNum = infoset;
		mListOfActions = actions;
		mListOfProbabilities = probabilities;
		mOutcome = outcome;

	}

	public Node(String name, int playerNo, int infoset, int outcome, String outcomeName) {

		mNodeName = name;
		mInfoSetNum = infoset;
		mOutcome = outcome;
		mOutcomeName =outcomeName;

	}
	
	public String getNodeName() {
		return mNodeName;
	}
	
	public int getInfoSetNumber() {
		return mInfoSetNum;
	}
	
	public String getInfoSetName() {
		return mInfoSetName;
	}
	
	public ArrayList<String> getActionsList(){
		return mListOfActions;
	}
	
	public ArrayList<Double> getProbabilitiees(){
		return mListOfProbabilities;
	}
	

}
