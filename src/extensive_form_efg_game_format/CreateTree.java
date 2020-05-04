package extensive_form_efg_game_format;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.Random;
import java.util.*;
import java.lang.*;

import javax.rmi.CORBA.Util;

import extensive_form_filemanager.CreateGambitEFGFile;
import utils.Utils;

public class CreateTree {
	private ArrayList<String> mChnaceNodeActionList;
	private ArrayList<String> realHostConfigList;
	private ArrayList<String> honeypotConfigLIst;
	private ArrayList<String> featuresVector;
	private ArrayList<Double> mChanceNodeProbablityList;
	private ArrayList<String> operatorsCombinations;
	private ArrayList<double[]> deltaCombinations;
	private CreateGambitEFGFile createGambitFile;
	private Hashtable<String, Integer> mBinarytoIntNumbers;
	public Hashtable<String, Double> realSystemProbabilities;
	public Hashtable<String, Double> honeypotProbabilites;
	public Hashtable<String, Integer> p2InformationSet;
	public Hashtable<String, Integer> p2InfoClass;
	private Node mChanceNode;
	private int mChaceInfoSetNo = 1;
	private int mTotalFeatures = Utils.TOTAL_FEATUES_NUMBER_IN_GAME;
	private int mOutcomeCnt;
	private int p2InfoSetCnt = 0;
	private int defenderActionsCnt = 0;
	private double[] classValues;
	private boolean isModifyRealSystem = false;
	private boolean isModifyBothSystem = true;
	private double[] realFeatureDistribution;// = new double[(int)Math.pow(2.0,(double) Utils.REAL_HOST_FEATURES_NUM)];
	private double[] honeypotFeatureDistribution;// = new double[(int)Math.pow(2.0,(double)
													// Utils.REAL_HOST_FEATURES_NUM)];
	private double[] deltaValues = {0.1, 0.2, 0.3};
	private Hashtable<Character, Double> modificationCostsByOperator;
	private Hashtable<Double, Double> modificationCostByDelta;
	
	private String operators = "!+-";

	public CreateTree(String filename, boolean isModifyBOth, double[] realProb, double[] hpProb) {
		createGambitFile = new CreateGambitEFGFile(filename);
		isModifyBothSystem = isModifyBOth;
		realFeatureDistribution = realProb;
		honeypotFeatureDistribution = hpProb;
	}

	public void init() {
		mOutcomeCnt = 0;
		classValues = new double[2];
		mChnaceNodeActionList = new ArrayList<String>();
		realHostConfigList = new ArrayList<String>();
		honeypotConfigLIst = new ArrayList<String>();
		mChanceNodeProbablityList = new ArrayList();
		featuresVector = new ArrayList();
		operatorsCombinations = new ArrayList<String>();
		deltaCombinations = new ArrayList<double[]>();
		modificationCostsByOperator = new Hashtable<Character, Double>();
		modificationCostByDelta = new Hashtable<Double, Double>();
		//deltaValues = new double[Utils.TOTAL_DELTA_NUMBERS];
		mBinarytoIntNumbers = new Hashtable<>();
		realSystemProbabilities = new Hashtable<>();
		honeypotProbabilites = new Hashtable<>();
		p2InformationSet = new Hashtable<>();
		p2InfoClass = new Hashtable<>();
		generateAllPossibleOperatorCombination();
		generateAllPossibleDeltaCombination();
		setSystemValues();
		setModificationCost();
		addFeaturesInVector(featuresVector);
		generateNatureActions(Utils.TOTAL_FEATUES_NUMBER_IN_GAME);

		mChanceNode = new Node(Utils.CHANCE_NODE_NAME, mChaceInfoSetNo, mChnaceNodeActionList,
				mChanceNodeProbablityList, 0);
		createGambitFile.createChanceNode(mChanceNode.getNodeName(), mChanceNode.getInfoSetNumber(),
				mChanceNode.getActionsList(), mChanceNode.getProbabilitiees(), 0);

		movePlayerOne();
	}

	/* index 0 used for the cost rihtmost bit of network and so on */
	public void setModificationCost() {
		/* Modification cost for operators*/
		modificationCostsByOperator.put('!', 0.0); // for operator !
		modificationCostsByOperator.put('+',2.0);// for operator +
		modificationCostsByOperator.put('-',1.0); // for operator -
		
		/*Cost for delta*/
		modificationCostByDelta.put(deltaValues[0], 0.1);
		modificationCostByDelta.put(deltaValues[1], 0.5);
		modificationCostByDelta.put(deltaValues[2], 1.5);
		//modificationCostByDelta.put(deltaValues[3], 1.5);
	}
	

	public void setProbability(int numberOfFeature) {
		realSystemProbabilities.clear();
		honeypotProbabilites.clear();
		for (int i = 0; i < realHostConfigList.size(); i++) {
			realSystemProbabilities.put(realHostConfigList.get(i), realFeatureDistribution[i]);
			honeypotProbabilites.put(realHostConfigList.get(i), honeypotFeatureDistribution[i]);
		}

	}

	public void setSystemValues() {
		classValues[0] = 1.0;
		classValues[1] = 1.0;

	}

	public static String reverseStr(String str) {
		if (str == null) {
			return null;
		}
		int len = str.length();
		if (len <= 0) {
			return "";
		}
		char[] strArr = new char[len];
		int count = 0;
		for (int i = len - 1; i >= 0; i--) {
			strArr[count] = str.charAt(i);
			count++;
		}
		return new String(strArr);
	}

	public void generateNatureActions(int numOfFeature) {
		for (int i = 0; i < featuresVector.size(); i++)

		{
			String networkString = featuresVector.get(i);
			double probability = 1;
			mChanceNodeProbablityList.add(probability);
			mChnaceNodeActionList.add(networkString);
		}

	}

	private void movePlayerOne() {
		for (int i = 0; i < mChnaceNodeActionList.size(); i++) {
			ArrayList<String> actions = new ArrayList<>();
			ArrayList<Integer> modifiedClass = new ArrayList<>();
			ArrayList<String> operatorList = new ArrayList<String>();
			ArrayList<double[]> deltaList = new ArrayList<double[]>();
			String cAction = mChnaceNodeActionList.get(i);
			int infoNo = i;
			List<String> featureList = Arrays.asList(cAction.split(","));
			int itrNum = featureList.size();
			for (int l = 0; l < deltaCombinations.size(); l++) {
				double[] curDel = deltaCombinations.get(l);
				for (int j = 0; j < operatorsCombinations.size(); j++) {
					String modifiedStr = "";
					String oprStr = operatorsCombinations.get(j);
					for (int it = 0; it < itrNum; it++) {
						double d = Double.parseDouble(featureList.get(it));
						if (oprStr.charAt(it) == '+') {
							d += curDel[it];
						} else if (oprStr.charAt(it) == '-') {
							d -= curDel[it];
						}
						String strFormat = "%." + 1 + "f";
						String s = String.format(strFormat, d);
						modifiedStr += s;
						if (it != itrNum - 1)
							modifiedStr += ",";
					}
					//System.out.println(modifiedStr + " : " + oprStr + " : " + Arrays.toString(curDel));

					    if(p2InfoClass.containsKey(modifiedStr) && p2InfoClass.get(modifiedStr) == i)
							continue;
						p2InfoClass.put(modifiedStr, i);
				        setP2InformationSet(modifiedStr, i);
						actions.add(modifiedStr);
						modifiedClass.add(i);
						operatorList.add(oprStr);
						deltaList.add(curDel);
					
					
				}
		}
			System.out.println("size " + actions.size());
			Utils.numOfDefenderActions = actions.size();
			createGambitFile.createPlayerNode(Utils.PLAYER_NODE_NAME, Utils.PLAYER_ONE, infoNo, cAction, actions, 0);

			for (int k = 0; k < actions.size(); k++) {
				movePlayerTwo(actions.get(k), modifiedClass.get(k), operatorList.get(k), deltaList.get(k),infoNo,
						mChnaceNodeActionList.get(i));
				// System.out.println(actions.get(k));
			}
			if (null != actions) {
				actions.clear();
				actions = null;
			}

		}
	}

	private void movePlayerTwo(String p1ModifiedAction, int cls, String optrs, double[] deltas, int palyerOneInfoSet,
			String natureAction) {

		ArrayList<String> actions = new ArrayList<>();
		String cl_1 = "Class_1";
		String cl_2 = "Class_2";
		actions.add(cl_1);
		actions.add(cl_2);
		// String p2InfoSet = getP2InofrmationSet(p1ModifiedAction); // Making same
		// infoset for both real and HP
		// int infosetNo = mBinarytoIntNumbers.get(p2InfoSet); // playerOne action was
		// used previously. For creating uncertainity for player2 new information set is
		// used.
		int infosetNo = getP2InofrmationSet(p1ModifiedAction);
		createGambitFile.createPlayerNode(Utils.PLAYER_NODE_NAME, Utils.PLAYER_TWO, infosetNo, p1ModifiedAction,
				actions, 0);
		setTerminalNode(actions, cls, optrs, deltas, p1ModifiedAction, palyerOneInfoSet, natureAction);
	}

	private double getModificationCostByOperator(char key) {

		return modificationCostsByOperator.get(key);

	}
	
	private double getModificationCostByOperator(double key) {

		return modificationCostByDelta.get(key);

	}

	private void setTerminalNode(List actions, int cl, String operator, double[] deltas, String playerOneAction, int playerOneInfoSet,
			String natureAction) {
		double cost = 0;
		for (int i = 0; i < operator.length(); i++) {
			cost += (getModificationCostByOperator(operator.charAt(i))* getModificationCostByOperator(deltas[i]));
			//System.out.println(getModificationCostByOperator(deltas[i]) + " ");
		}
		//System.out.println();
		ArrayList<Double> payoffs = new ArrayList<>();
		for (int k = 0; k < actions.size(); k++) {

			if (payoffs.size() != 0)
				payoffs.clear();
			double payoff = classValues[cl];
			if (cl == 0 && actions.get(k).equals("Class_1")) {
				payoffs.add(-(cost + payoff));
				payoffs.add(payoff);
			} else if (cl == 0 && actions.get(k).equals("Class_2")) {
				payoffs.add(payoff - cost);
				payoffs.add(-payoff);
			} else if (cl == 1 && actions.get(k).equals("Class_2")) {
				payoffs.add(-(cost + payoff));
				payoffs.add(payoff);
			} else {
				payoffs.add(payoff - cost);
				payoffs.add(-(payoff));
			}

			createGambitFile.createTerminalNode(Utils.TERMINAL_NODE_NAME, ++mOutcomeCnt, "Outcome " + mOutcomeCnt,
					payoffs);
		}

	}

	public int getP2InofrmationSet(String action) {
		return p2InformationSet.get(action);
	}

	public void setP2InformationSet(String networkConfig, int cls) {

		if (!p2InformationSet.containsKey(networkConfig)) {
			// System.out.println(networkConfig + " Network String");
			p2InformationSet.put(networkConfig, p2InfoSetCnt++);
		}else
		{
			//System.out.println("Found value : " + networkConfig);
		}
		

	}

	/*
	 * public void setP2InformationSet(String realHost, String hp) {
	 * 
	 * String realNetworkConfig = realHost+ hp; String imperfectNetwrokConfig = hp +
	 * realHost; String infoSet = realHost+hp;
	 * if(!p2InformationSet.contains(realNetworkConfig) &&
	 * !p2InformationSet.contains(imperfectNetwrokConfig)) {
	 * System.out.println(realNetworkConfig + " : " + infoSet);
	 * p2InformationSet.put(realNetworkConfig, infoSet); } if(!realHost.equals(hp)
	 * && !p2InformationSet.contains(imperfectNetwrokConfig)) {
	 * p2InformationSet.put(imperfectNetwrokConfig,infoSet);
	 * System.out.println(imperfectNetwrokConfig + " : " + infoSet); }
	 * 
	 * }
	 */
	
	private void generateAllPossibleDeltaCombination() {
		permutation(new double[Utils.REAL_HOST_FEATURES_NUM], 0, deltaValues);
	}
	private void generateAllPossibleOperatorCombination() {

		char[] perm = new char[Utils.REAL_HOST_FEATURES_NUM];
		permutation(perm, 0, operators);
	}

	private void permutation(char[] perm, int pos, String str) {
		if (pos == perm.length) {
			operatorsCombinations.add(new String(perm));
		} else {
			for (int i = 0; i < str.length(); i++) {
				perm[pos] = str.charAt(i);
				permutation(perm, pos + 1, str);
			}
		}
	}
	
	private  void permutation(double[] perm, int pos, double[] nums) {
	    if (pos == perm.length) {
	    	double[] res = new double[perm.length];
	    	 for(int k = 0; k<perm.length; k++)
	            res[k] = perm[k];
	    	deltaCombinations.add(res);
	    } else {
	        for (int i = 0 ; i < nums.length; i++) {
	            perm[pos] = nums[i];
	            permutation(perm, pos+1, nums);
	        }
	    }
	}	
		
	public void closeFile() {
		createGambitFile.closeFile();
	}

	public void addFeaturesInVector(ArrayList<String> featureVec) {
		String class1 = "" + 3.2 + "," + 0.9; // class1
		String class2 = "" + 3.0 + "," + 0.7; // class2
		featureVec.add(class1);
		featureVec.add(class2);  
		

	}

}
