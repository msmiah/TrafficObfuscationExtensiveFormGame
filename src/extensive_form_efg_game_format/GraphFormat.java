package extensive_form_efg_game_format;

import java.util.List;

public interface GraphFormat {
	public void createChanceNode(String nodeName, int informationSet, List actions, List probabilites, int payoff);
	public void createPlayerNode(String name, int playerNo, int infoset, String infosetName, List actions, int outcome);
	public void createTerminalNode(String name, int outcome, String outcomeName, List payoffs);

}
