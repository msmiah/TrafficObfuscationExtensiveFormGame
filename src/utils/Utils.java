package utils;

public class Utils {
	public static final String PLAYER_ONE_NAME = "Defender";
	public static final String PLAYER_TWO_NAME = "Attacker";
	public static final int DEFENDER_INFO_SET_NUMBER = 1;
	public static final int ATTACKER_INFO_SET_NUMBER = 2;
	public static final int PLAYER_ONE = DEFENDER_INFO_SET_NUMBER;
	public static final int PLAYER_TWO = ATTACKER_INFO_SET_NUMBER;
	public static final int TOTAL_NUM_OF_REAL_HOST= 1;
	public static final int TOTAL_NUM_OF_HONEYPOT = 1;
	public static final int REAL_HOST_FEATURES_NUM = 2;
	public static final int HONEYPOT_FEATURES_NUM = REAL_HOST_FEATURES_NUM;
	public static final int TOTAL_FEATUES_NUMBER_IN_GAME = (REAL_HOST_FEATURES_NUM * TOTAL_NUM_OF_REAL_HOST) + (HONEYPOT_FEATURES_NUM * TOTAL_NUM_OF_HONEYPOT);
	public static final String EFG_FILE_SAVING_PATH = ""; 
	public static final String FILE_FORMAT=".efg";
	public static final String CHANCE_NODE_NAME = "c";
	public static final String PLAYER_NODE_NAME = "p";
	public static final String TERMINAL_NODE_NAME = "t";
	public static final int TOTAL_DELTA_NUMBERS = 3;
	
	public static int numOfDefenderActions = 0;
	public static int MAX_NO_ATTACKER_ACTIONS = TOTAL_NUM_OF_REAL_HOST + TOTAL_NUM_OF_HONEYPOT;
	public static final int NUM_INFO_SET_PLAYER_1=200000;
	public static final int NUM_INFO_SET_PLAYER_2 = 1000000;
	public static final int  TOTAL_NUMBER_OF_NODE = 1000000;//357;
	public static final double PLAYER_ONE_MAX_VAL = 5000;
	
	public static final int NUM_ACTION_IN_EACH_FEATURE = 2 ;
	

}
