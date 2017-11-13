/*
 * @Environment: JavaSE-1.8
 * @Author: wpaladins
 * @Time: 2017/10-2017/11
 */
import java.io.BufferedReader;/**Need it in NFA2DFA**/
import java.io.File;/**Need it to out to file**/
import java.io.FileNotFoundException;
import java.io.FileOutputStream;/**Need it to out to file**/
import java.io.FileReader;/**Need it in NFA2DFA**/
import java.io.PrintStream;/**Need it to out to file**/
import java.util.ArrayList;/**Need it to Analysis**/
import java.util.HashMap;/**Need it in MinimizeDFA**/
import java.util.HashSet;
import java.util.LinkedList;/**Need it in NFA2DFA**/
import java.util.Queue;/**Need it in NFA2DFA**/
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;

public class Analysis {
	
	static PrintStream pnfa;
	static PrintStream pdfa;
	static PrintStream pminidfa;
	//new
	static PrintStream pnewnfa;
	static PrintStream pnewdfa;
	static PrintStream pnewminidfa;
	
	//为了存储全部的转移表
	static Set<TransferTable> transferTables;
	//为了存储源程序
	static StringBuffer sourceProgram;
	//为了存储Token序列
	static ArrayList<Token> tokens;
	//为了能够存储当前操作到源程序的什么位置
	static int pointer;
	
	public static void main(String[] args) throws FileNotFoundException {
		
		//为了输出到文件做一下操作：
		FileOutputStream fs1 = new FileOutputStream(new File("..\\show\\js\\abuse.js"));
		FileOutputStream fs2 = new FileOutputStream(new File("..\\show\\js\\abuse.js"));
		FileOutputStream fs3 = new FileOutputStream(new File("..\\show\\js\\abuse.js"));
		FileOutputStream fs4 = new FileOutputStream(new File("..\\show\\js\\re.js"));
		pnfa = new PrintStream(fs1);
		pdfa = new PrintStream(fs2);
		pminidfa = new PrintStream(fs3);
		PrintStream pre = new PrintStream(fs4);
		//new
		FileOutputStream newfs1 = new FileOutputStream(new File("..\\show\\newnfa\\data.js"));
		FileOutputStream newfs2 = new FileOutputStream(new File("..\\show\\newdfa\\data.js"));
		FileOutputStream newfs3 = new FileOutputStream(new File("..\\show\\newminidfa\\data.js"));
		pnewnfa = new PrintStream(newfs1);
		pnewdfa = new PrintStream(newfs2);
		pnewminidfa = new PrintStream(newfs3);
		//new init
		pnewnfa.print("var data = \"digraph {\\n" + 
				"    node [rx=5 ry=5 labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\" style=\\\"fill: rgb(179, 226, 10); font-weight: bold\\\"]\\n" + 
				"    edge [labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\"]\\n");
		pnewdfa.print("var data = \"digraph {\\n" + 
				"    node [rx=5 ry=5 labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\" style=\\\"fill: rgb(179, 226, 10); font-weight: bold\\\"]\\n" + 
				"    edge [labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\"]\\n");
		pnewminidfa.print("var data = \"digraph {\\n" + 
				"    node [rx=5 ry=5 labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\" style=\\\"fill: rgb(179, 226, 10); font-weight: bold\\\"]\\n" + 
				"    edge [labelStyle=\\\"font: 300 14px 'Helvetica Neue', Helvetica\\\"]\\n");
		
		//读入一个正则表达式，允许有(、)、*、|
		Scanner scanner = new Scanner((Readable) new BufferedReader(new FileReader(".\\input.txt")));
		String re = scanner.nextLine();
		scanner.close();
		//将读入的内容分割并存入
		String[] array = re.split(" ");
		re = array[1];
		System.out.print(re);
		
		//将re打印到JS文件中
		pre.println("var re = \"" + re + "\";");
		pre.close();
		
		//将正则表达式中的与运算转化为+号
		re = add_join_symbol(re);
		//System.out.println(re);
		
		//将正则表达式转为Cell
		Cell NFA = postfix_expression(re);
		//处理NFA中的状态，为了输出到js才加的
		for(Edge e:NFA.edges) {
			NFA.states.add(e.startState);
			NFA.states.add(e.endState);
		}
		
		System.out.println("=======================================================================================================");
		System.out.println("# The information of NFA:");
		System.out.println("-------------------------");
		NFA.Print();
		System.out.println("=======================================================================================================");
		
		/**********************从这里开始，开始写NFA转DFA的操作**********************/
		
		DFA DFA = NFA2DFAmethod(NFA,re);
		
		System.out.println("# The information of DFA:");
		System.out.println("-------------------------");
		DFA.Print();
		System.out.println("=======================================================================================================");
		
		/**********************从这里开始，开始写DFA最小化的操作**********************/
		
		miniDFA  miniDFA= MinimizeDFAmethod(DFA,re);
		
		System.out.println("# The information of MiniDFA:");
		System.out.println("-----------------------------");
		miniDFA.Print();
		System.out.println("=======================================================================================================");
		
		//将信息输出到JS并且
		NFA.printToJS();
		DFA.printToJS();
		miniDFA.printToJS();
		//pnew的最后处理
		pnewnfa.print("}\"");
		pnewdfa.print("}\"");
		pnewminidfa.print("}\"");
		//关闭输出到文件的指针
		pnfa.close();
		pdfa.close();
		pminidfa.close();
		pnewnfa.close();
		pnewdfa.close();
		pnewminidfa.close();
		
		/**********************从这里开始，开始写词法分析程序的生成程序的操作**********************/
		
		transferTables = new HashSet<TransferTable>();
		generateTransferTables();
		readSourceProgram();
		generateTokens();
		printTokens();
	}
	
	//完成将正则表达式中的与运算转化为+号(2017/10/18-22:02)
	public static String add_join_symbol(String re) {
		StringBuffer new_re = new StringBuffer();
		for (int i = 0; i < re.length() - 1; i++) {
			Character first = re.charAt(i);
			Character second = re.charAt(i + 1);
			new_re.append(first);
			//若第二个是字母、第一个不是'('、'|'都要添加
			if (Character.isLetter(second) && !first.equals('(') &&!first.equals('|') ) {
				new_re.append('+');
			}
			//若第二个是'(',第一个不是'|'、'(',也要加
			else if (second.equals('(') && !first.equals('(') &&!first.equals('|') ) {
				new_re.append('+');
			}
		}
		new_re.append(re.charAt(re.length() - 1));
		return new_re.toString();
	}
	
	//正则表达式的优先级表
	static String op_priority[][] = {
			/*           当前操作符                   */
			/*           +    |    *    (    )    # */
		{   /* 栈 + */  ">", "<", "<", "<", ">", ">"}, //+ 0 （双目）
		{   /* 顶 | */  ">", ">", "<", "<", ">", ">"}, //| 1 （双目）
		{   /* 操 * */  ">", ">", ">", "x", ">", ">"}, //* 2 （单目）
		{   /* 做 ( */  "<", "<", "<", "<", "=", "x"}, //( 3 不可能大于当前操作符
		{   /* 符 ) */  "x", "x", "x", "x", "x", "x"}, //) 4 不可能出现在栈顶
		{   /*    # */  "<", "<", "<", "<", "x", "="}  //# 5
	};
	
	//从操作符号向对应数字的转换
	static int op_symbol2int(String op_symbol) {
		switch(op_symbol) {
		case "+":
			return 0;
		case "|":
			return 1;
		case "*":
			return 2;
		case "(":
			return 3;
		case ")":
			return 4;
		case "#":
			return 5;
		}
		return -1;
	}
	
	//通过栈顶操作符和当前操作符查询栈顶操作符是否大于当前操作符
	//在要完成从操作符号向对应数字的转换
	static int is_bigger(String op_top, String op_now) {
		//System.out.println(op_priority[op_symbol2int(op_top)][op_symbol2int(op_now)]);
		if(op_priority[op_symbol2int(op_top)][op_symbol2int(op_now)].equals(">")) {
			return 1;
		}
		else if(op_priority[op_symbol2int(op_top)][op_symbol2int(op_now)].equals("=")) {
			return 0;
		}
		else if(op_priority[op_symbol2int(op_top)][op_symbol2int(op_now)].equals("<")) {
			return -1;
		}
		return -2;
	}
	
	//用来处理*
	static Cell handle(String op_symbol_tohandle, Cell op_char_tohandle) {
		//新建一个存最后结果的Cell名为newCell
		Cell newCell = new Cell();
		//通过Thompson算法进行处理
		newCell.edges.addAll(op_char_tohandle.edges);
		Edge edge;
		//添加四条空边
		edge = new Edge(newCell.startState,op_char_tohandle.startState);
		newCell.edges.add(edge);
		edge = new Edge(op_char_tohandle.endState,newCell.endState);
		newCell.edges.add(edge);
		edge = new Edge(newCell.startState,newCell.endState);
		newCell.edges.add(edge);
		edge = new Edge(op_char_tohandle.endState,op_char_tohandle.startState);
		newCell.edges.add(edge);
		return newCell;
	}
	
	//用来处理+和|
	static Cell handle(String op_symbol_tohandle,Cell op_char1_tohandle,Cell op_char2_tohandle) {
		Cell newCell = new Cell();
		newCell.edges.addAll(op_char1_tohandle.edges);
		newCell.edges.addAll(op_char2_tohandle.edges);
		
		Edge edge;
		switch(op_symbol_tohandle) {
		case "+":
		{
			edge = new Edge(newCell.startState,op_char1_tohandle.startState);
			newCell.edges.add(edge);
			edge = new Edge(op_char2_tohandle.endState,newCell.endState);
			newCell.edges.add(edge);
			edge = new Edge(op_char1_tohandle.endState,op_char2_tohandle.startState);
			newCell.edges.add(edge);
			break;
		}
		case "|":
		{
			edge = new Edge(op_char1_tohandle.endState,newCell.endState);
			newCell.edges.add(edge);
			edge = new Edge(op_char2_tohandle.endState,newCell.endState);
			newCell.edges.add(edge);
			edge = new Edge(newCell.startState,op_char1_tohandle.startState);
			newCell.edges.add(edge);
			edge = new Edge(newCell.startState,op_char2_tohandle.startState);
			newCell.edges.add(edge);
			break;
		}//case
		}//switch
		return newCell;
	}
	
	//完成正则表达式的中缀表达式
	//写之中需要完成op_priority优先级表和
	//通过栈顶操作符和当前操作符查询栈顶操作符是否大于当前操作符的函数is_bigger
	//写之中需要完成to_handle用来处理
	static Cell postfix_expression(String re) {
		StringBuffer new_re = new StringBuffer();
		new_re = new_re.append(re);
		new_re = new_re.append("#");//给re之后加入#
		//System.out.println(new_re);
		
		//delete : Stack<String> op_char = new Stack<String>();
		Stack<String> op_symbol = new Stack<String>();
		Stack<Cell> op_char_cell = new Stack<Cell>();
		op_symbol.push("#");
		
		int i;
		String reg = "+|*()#";
		//按照规则进行处理
		for(i = 0 ; i < new_re.length(); i++) {
			Character c = new_re.charAt(i);
			//System.out.print(reg.indexOf(c) != -1);
			if(reg.indexOf(c) != -1) {//判断是不是操作符，如果是的话
				//System.out.print(is_bigger(op_symbol.peek(),c.toString()) == 1);
				while(is_bigger(op_symbol.peek(),c.toString()) == 1) {//如果栈内操作符比当前操作符的优先级高的话
					String op_symbol_tohandle = op_symbol.pop();
					if(op_symbol_tohandle.equals("*")) {//如果栈内操作符是*的话
						Cell op_char_cell_tohandle = op_char_cell.pop();
						Cell newCell = handle(op_symbol_tohandle,op_char_cell_tohandle);
						op_char_cell.push(newCell);
					}
					else {//如果栈内操作符是+或者|的话
						Cell op_char2_cell_tohandle = op_char_cell.pop();
						Cell op_char1_cell_tohandle = op_char_cell.pop();
						Cell newCell = handle(op_symbol_tohandle,op_char1_cell_tohandle,op_char2_cell_tohandle);
						op_char_cell.push(newCell);
					}
				}
				if(is_bigger(op_symbol.peek(),c.toString()) == -1) {
					op_symbol.push(c.toString());
				}
				if(!op_symbol.isEmpty() & is_bigger(op_symbol.peek(),c.toString()) == 0) {
					op_symbol.pop();
				}
			}
			else {//如果不是操作符的话
				Cell newCell = new Cell(c.toString());
				op_char_cell.push(newCell);
			}
		}
		//System.out.println();
		return op_char_cell.peek();
	}
	
	/**********************从这里开始，开始写NFA转DFA的函数**********************/
	
	//求状态的eps闭包
	static Set<State> eps_closure(State startState,Cell NFA) {
		Set<State> new_state_set = new HashSet<State>();//用来存储需要需要返回的所有状态的集合
		Queue<State> states_tohandle = new LinkedList<State>();//用来存储需要判断是不是在eps
		new_state_set.add(startState);
		states_tohandle.add(startState);	
		
		while(!states_tohandle.isEmpty()) {
			State state_tohandle = states_tohandle.poll();
			for(Edge e: NFA.edges) {
				if(e.startState.equals(state_tohandle) && e.transSymbol.equals("eps")) {
					new_state_set.add(e.endState);
					states_tohandle.add(e.endState);
				}
			}
		}

		return new_state_set;
	}
	
	//求NFA中从DFA_State t中的每一个状态出发，经过转换字符c到达的所有状态的集合
	static Set<State> delta(DFA_State t,Character c,Cell NFA) {
		Set<State> newStateSet = new HashSet<State>();
		for(State startState:t.states) {
			for(Edge e: NFA.edges) {
				if(e.startState.equals(startState) && e.transSymbol.equals(c.toString())) {
					newStateSet.add(e.endState);
				}
			}
		}
		return newStateSet;
	}
	
	//求所有states集合中的状态在NFA中的eps闭包，并将最终的所有结果作为一个集合返回
	static Set<State> eps_closure(Set<State> states,Cell NFA) {
		Set<State> newStateSet = new HashSet<State>();
		newStateSet.addAll(states);
		for(State s: states) {
			newStateSet.addAll(eps_closure(s,NFA));
		}
		return newStateSet;
	}
	
	//get_newq_InQ，返回在Q中与newq中内容相同的DFA_State
	static DFA_State get_newq_InQ(Set<DFA_State> Q,DFA_State newq) {
		for(DFA_State q: Q) {
			if(q.states.size() != newq.states.size()) {//如果长度不同，直接不做判断
				continue;
			}
			int num = 0;
			for(State state: q.states) {
				if(newq.states.contains(state)) {
					num++;
				}
			}
			if(num == q.states.size()) {
				return q;
			}
		}
		return null;
	}
	
	//isNotInDFAEdges(DFA_Edge,DFA)，判断边DFA_Edge在DFA中是否存在
	static boolean isNotInDFAEdges(DFA_Edge newDFAEdge,DFA newDFA) {
		for(DFA_Edge DE: newDFA.DFAEdges) {
			if(DE.startDFAState.equals(newDFAEdge.startDFAState) & DE.endDFAState.equals(newDFAEdge.endDFAState) ) {
				return false;
			}
		}
		return true;
	}
	
	//写的过程中需要完成的函数
	//eps_closure(startState,NFA)，实现求一个状态再NFA中的eps闭包
	//delta(DFA_State t,c,NFA)，实现求NFA中从DFA_State t中的每一个状态出发，经过转换字符c到达的酥油状态的集合
	//eps_closure(Set<State> states,NFA)，求所有states集合中的状态在NFA中的eps闭包，并将最终的所有结果作为一个集合返回
	//get_newq_InQ，返回在Q中与newq中内容相同的DFA_State
	//isNotInDFAEdges(DFA_Edge,DFA)，判断边DFA_Edge在DFA中是否存在
	static DFA NFA2DFAmethod (Cell NFA,String re) {
		//新建了一个新的DFA来存储接下来的一切对DFA的创建操作
		DFA newDFA = new DFA();
		//里面装了所有状态的集合，为了判断状态是不是已经存在
		Set<DFA_State> Q = new HashSet<DFA_State>();
		//里面装了还没有被处理的状态态组成的队列
		Queue<DFA_State> worklist = new LinkedList<DFA_State>();
		
		//创建DFA的第一个状态并且将它放入DFA中
		DFA_State q0 = new DFA_State(eps_closure(NFA.startState,NFA),NFA);
		Q.add(q0);worklist.add(q0);
		
		//为了找出正则表达式中的非符号的，创建一个符号都在的字符串
		String op = "+|()*";
		while(!worklist.isEmpty()) {
			DFA_State q = worklist.poll();
			for(int i = 0;i < re.length();i++) {//对每个正则表达式中出现过的转换字符的值，进行判断
				if(op.indexOf(re.charAt(i)) != -1) {
					continue;
				}
				DFA_State newq = new DFA_State(eps_closure(delta(q,re.charAt(i) ,NFA) ,NFA) ,NFA);
				if(newq.states.isEmpty()) {
					DFA_State.number--;
				}
				else if(get_newq_InQ(Q,newq) == null) {
					Q.add(newq);worklist.add(newq);
					DFA_Edge newDFAEdge = new DFA_Edge(q,newq,re.charAt(i));
					if(isNotInDFAEdges(newDFAEdge,newDFA)) {
						newDFA.DFAEdges.add(newDFAEdge);
					}
				}
				else {
					DFA_Edge newDFAEdge = new DFA_Edge(q,get_newq_InQ(Q,newq),re.charAt(i));
					if(isNotInDFAEdges(newDFAEdge,newDFA)) {
						newDFA.DFAEdges.add(newDFAEdge);
					}
					DFA_State.number--;
				}
			}
		}
		newDFA.DFAStates.addAll(Q);
		return newDFA;
	}
	
	/**********************从这里开始，开始写DFA最小化的函数**********************/
	
	static miniDFAState getMiniDFAStateDFAStateIn(DFA_State DFAState,Set<miniDFAState> miniDFAStatesNow) {
		for(miniDFAState MDS: miniDFAStatesNow) {
			if(MDS.DFAStates.contains(DFAState)) {
				return MDS;
			}
		}
		return null;
	}
	
	//在写之前需完成getMiniDFAStateDFAStateIn()函数
	static Set<miniDFAState> split(miniDFAState mDS,String re,DFA DFA,Set<miniDFAState> miniDFAStatesNow) {
		Set<miniDFAState> newMiniDFAStateSet = new HashSet<miniDFAState>();
		
		//对于每一个转换字符
		String op = "+|()*";
		for(int i = 0;i < re.length();i++) {
			if(op.indexOf(re.charAt(i)) != -1) {
				continue;
			}
			
			//此处表示re.charAt(i)已经是一个transSymbol
			Character ch = re.charAt(i);
			
			//用键值对来存储每一个状态以及它通过当前转换字符到达的miniDFAState
			HashMap<DFA_State,miniDFAState> map = new HashMap<DFA_State,miniDFAState>();
			for(DFA_Edge DFAEdge:DFA.DFAEdges) {
				if(mDS.DFAStates.contains(DFAEdge.startDFAState) && DFAEdge.transSymbol.equals(ch.toString())) {
					miniDFAState k = getMiniDFAStateDFAStateIn(DFAEdge.endDFAState,miniDFAStatesNow);
					map.put(DFAEdge.startDFAState, k);
				}
			}
			
			for(DFA_State DS: mDS.DFAStates) {
				if(!map.containsKey(DS)) {
					map.put(DS, mDS);
				}
			}
			
			//判断map的值中有几种miniDFAState了
			Set<miniDFAState> newSetMiniDFAState = new HashSet<miniDFAState>();
			for(DFA_State DS: map.keySet()) {
				newSetMiniDFAState.add(map.get(DS));
			}
			int numberOfMiniDFAState = newSetMiniDFAState.size();
			
			if(numberOfMiniDFAState == 1) {
				continue;
			} else {
				for(miniDFAState MDS: newSetMiniDFAState) {//对于每一个最终状态
					miniDFAState newMiniDFAState = new miniDFAState();//新建一个miniDFAState
					for(DFA_State DS: map.keySet()) {//判断map中的每一个键值对
						//如果当前值为MDS，则将键加入新的newMiniDFAState的DFAStates中
						if(map.get(DS) == MDS) {
							newMiniDFAState.DFAStates.add(DS);
						}
					}
					//将newMiniDFAState加入到newMiniDFAStateSet
					newMiniDFAStateSet.add(newMiniDFAState);
				}
			}
			return newMiniDFAStateSet;
		}
		newMiniDFAStateSet.add(mDS);
		return newMiniDFAStateSet;
	}
	
	//写的过程中需要完成的函数
	//split
	static miniDFA MinimizeDFAmethod(DFA DFA,String re) {
		miniDFA newMiniDFA = new miniDFA();
		/**在这里实现hopcroft算法**/
		//新建miniDFAState状态N和A并初始化
		miniDFAState N = new miniDFAState(), A = new miniDFAState();
		for(DFA_State DS: DFA.DFAStates) {
			if(DS.isExitState) {//可接受状态，进入A
				A.DFAStates.add(DS);
			}
			else {
				N.DFAStates.add(DS);
			}
		}
		//新建处理队列以及最终的miniDFAState集合
		Set<miniDFAState> miniDFAStates =  new HashSet<miniDFAState>();//用来存储最终的miniDFAState
		LinkedList<miniDFAState> worklist = new LinkedList<miniDFAState>();
		Set<miniDFAState> miniDFAStatesNow =  new HashSet<miniDFAState>();//用来存储当前的miniDFAState
		//将N和A添加到处理队列中
		worklist.add(N);worklist.add(A);miniDFAStatesNow.add(A);miniDFAStatesNow.add(N);
		//开始处理
		while(!worklist.isEmpty()) {//如果worklist不空，则说明还有没有处理完的状态
			miniDFAState DS = worklist.pop();//拿出来一个来处理
			Set<miniDFAState> newMiniDFAState = split(DS,re,DFA,miniDFAStatesNow);//去分割一次
			if(newMiniDFAState.size() == 1) {//如果返回的集合的size为1，则为miniDFA状态
				miniDFAStates.addAll(newMiniDFAState);
			}
			else {//如果不是1，则将其中的每一个新的状态添加到worklist中等待处理
				for(miniDFAState mDS: newMiniDFAState) {
					worklist.add(mDS);
					miniDFAStatesNow.add(mDS);
				}
			}
		}
		//为每一个miniDFAState起名字并且判断并设置它是不是可接受状态或者进入状态
		for(miniDFAState mDS: miniDFAStates) {
			mDS.set();
		}
		//通过对DFA中的每一条边的遍历判断，为miniDFA增加边
		//首先建立DFA中每一个状态到miniDFA中状态的键值转换关系
		HashMap<DFA_State,miniDFAState> map = new HashMap<DFA_State,miniDFAState>();
		for(miniDFAState mDS: miniDFAStates) {
			for(DFA_State DS: mDS.DFAStates) {
				map.put(DS, mDS);
			}
		}
		LinkedList<miniDFAEdge> miniDFAEdges = new LinkedList<miniDFAEdge>();
		for(DFA_Edge DE: DFA.DFAEdges) {
			miniDFAEdge newMiniDFAEdge = new miniDFAEdge(map.get(DE.startDFAState),map.get(DE.endDFAState),DE.transSymbol);
			miniDFAEdges.add(newMiniDFAEdge);
		}
		//去除重复的边
		for(int i = 0; i < miniDFAEdges.size(); i++) {
			boolean flag = false;
			for(int j = i + 1; j< miniDFAEdges.size(); j++) {
				if(miniDFAEdges.get(i).startMiniDFAState == miniDFAEdges.get(j).startMiniDFAState && miniDFAEdges.get(i).endMiniDFAState == miniDFAEdges.get(j).endMiniDFAState && miniDFAEdges.get(i).transSymbol.equals(miniDFAEdges.get(j).transSymbol)) {
					miniDFAEdges.remove(i);
					flag = true;
					break;
				}
			}
			if(flag) {//删了之后需要删除当前元素，所以i-1一下，这样才不会有遗漏
				i--;
			}
		}
		//将结果添加保存到newMiniDFA中
		newMiniDFA.miniDFAStates.addAll(miniDFAStates);
		newMiniDFA.miniDFAEdges.addAll(miniDFAEdges);
		return newMiniDFA;
	}
	
	/**********************从这里开始，开始写词法分析程序的生成程序的函数**********************/
	
	static void generateTransferTables() throws FileNotFoundException {
		//1. 一行一行读入正则表达式们
		Scanner scanner = new Scanner((Readable) new BufferedReader(new FileReader(".\\input.txt")));
		ArrayList<String> res = new ArrayList<String>();
		while(scanner.hasNextLine()) {
			res.add(scanner.nextLine());
		}
		//关闭scanner
		scanner.close();
		//2. 对每一个正则表达式，进行分析得到其MiniDFA
		for(String re: res){
			//新建表
			TransferTable newTable = new TransferTable();
			
			//将读入的内容分割并存入
			String[] array = re.split(" ");
			newTable.tableName = array[0];
			re = array[1];
			//如果tableName不是punctuation、number、reservedWord、id中的某一个，continue；
			if(!newTable.tableName.equals("punctuation") && !newTable.tableName.equals("number") && !newTable.tableName.equals("reservedWord") && !newTable.tableName.equals("id")) {
				continue;
			}
			
			//System.out.println(re);
			
			//转换成MiniDFA
			re = add_join_symbol(re);
			Cell NFA = postfix_expression(re);
			DFA DFA = NFA2DFAmethod(NFA,re);
			miniDFA  miniDFA= MinimizeDFAmethod(DFA,re);
			
			//3. 将每一个得到的MiniDFA转换成表，并加入到transferTables
			//新建表的每一行
			for(miniDFAState mDS: miniDFA.miniDFAStates) {//对于每一个节点
				HashMap<String,String> newLine = new HashMap<String,String>();//新建一行
				for(miniDFAEdge mDE: miniDFA.miniDFAEdges) {//对于每一条边
					if(mDE.startMiniDFAState == mDS) {//如果边的起始节点是这个节点
						newLine.put(mDE.transSymbol, mDE.endMiniDFAState.miniDFAStateName);//新建一个键值对，键为转换字符，值为到达的节点，并将键值对加入到这一行
					}
				}
				newTable.lines.put(mDS.miniDFAStateName, newLine);//将这一行加入到表中
				if(mDS.isEnterState) {
					newTable.enterState = mDS.miniDFAStateName;
				}
				if(mDS.isExitState) {
					newTable.acceptableState.add(mDS.miniDFAStateName);
				}
			}
			transferTables.add(newTable);
		}
	}
	
	static void readSourceProgram() throws FileNotFoundException {
		Scanner scanner = new Scanner((Readable) new BufferedReader(new FileReader(".\\sourceProgram.txt")));
		sourceProgram = new StringBuffer();
		while(scanner.hasNextLine()) {
			sourceProgram.append(scanner.nextLine());
		}
		scanner.close();
		//sourceProgram.append("\n	");
	}
	
	static void generateTokens() {
		System.out.println(sourceProgram);
		tokens = new ArrayList<Token>();
		for(pointer = 0; pointer < sourceProgram.length(); pointer++) {// 
			for(TransferTable transferTable: transferTables) {
				Token token = nextToken(transferTable);
				//System.out.println(pointer);
				int temp = pointer;
				if(token != null) {
					tokens.add(token);
				} else {
					pointer = temp;
				}
			}
		}
	}
	
	static Token nextToken(TransferTable transferTable) {
		Token newToken = new Token();
		StringBuffer tokenValue = new StringBuffer();
		
		String state = transferTable.enterState;
		Stack<String> stateStack = new Stack<String>();
		
		Character ch;
		
		if(pointer == sourceProgram.length()) {
			return null;
		}
		
		//从pointer开始往后继续
		while(state != null) {
			ch = sourceProgram.charAt(pointer);
			pointer++;
			if(pointer == sourceProgram.length()) {
				break;
			}
			tokenValue.append(ch);
			if(transferTable.acceptableState.contains(state)) {
				stateStack.clear();
			}
			stateStack.push(state);
			state = transferTable.lines.get(state).get(ch.toString());
		}
		
		while(!transferTable.acceptableState.contains(state)) {
			if(stateStack.isEmpty()) {
				break;
			}
			state = stateStack.pop();
			//rollback
			pointer--;
			if(tokenValue.length() != 0) {
				tokenValue.deleteCharAt(tokenValue.length() - 1);
			}
		}
		
		if(tokenValue.length() == 0) {
			return null;
		}
		
		//将数据加入到tokenValue中
		if(transferTable.tableName.equals("id")) {
			newToken.type = "id";
			newToken.name = tokenValue.toString();
		} else if(transferTable.tableName.equals("reservedWord")) {
			newToken.type = "reservedWord";
			newToken.str = tokenValue.toString();
		} else if(transferTable.tableName.equals("punctuation")) {
			newToken.type = "punctuation";
			newToken.str = tokenValue.toString();
		} else if(transferTable.tableName.equals("number")) {
			newToken.type = "number";
			newToken.value = Integer.valueOf(tokenValue.toString());
		}
		return newToken;
	}
	
	static void printTokens() {
		for(Token token: tokens) {
			if(token.type.equals("id")) {
				System.out.println("id,name=" + token.name);
			} else if(token.type.equals("reservedWord")) {
				System.out.println("reserved word:" + token.str);
			} else if(token.type.equals("punctuation")) {
				System.out.println(token.str);
			} else if(token.type.equals("number")) {
				System.out.println("num,val=" + token.value);
			}
		}
	}
}

/**********************以下类为了RE2NFA**********************/

class State {
	static int number = 0;
	String stateName;
	
	State() {
		this.stateName = String.valueOf(State.number);
		State.number++;
	}
	
	public void Print() {
		System.out.print(stateName);
	}
	
	public void printToJS() {
		Analysis.pnfa.println("g.setNode(" + this.stateName + ", { label: \\\"" + this.stateName + "\\\" });");
		//new
		Analysis.pnewnfa.print("    " + this.stateName + " [label = \\\"" + this.stateName + "\\\" shape= \\\"ellipse\\\"];\\n");
	}
}

class Edge {
	State startState;
	State endState;
	String transSymbol;
	
	Edge(String transSymbol) {
		this.transSymbol = transSymbol;
		this.startState = new State();
		this.endState = new State();
	}
	Edge(State startState, State endState) {
		this.startState = startState;
		this.endState = endState;
		this.transSymbol = "eps";
	}
	
	public void Print() {
		System.out.print("NFAEdge From:");
		startState.Print();
		System.out.print(" To:");
		endState.Print();
		System.out.print(" TransSymbol:" + this.transSymbol);
		System.out.print("\n");
	}
	
	public void printToJS() {
		if(this.transSymbol.equals("eps")) {
			Analysis.pnfa.println("g.setEdge(" + this.startState.stateName + ", " + this.endState.stateName + ");");
			//new
			Analysis.pnewnfa.print("    " + this.startState.stateName + " -> " + this.endState.stateName + " [arrowhead = \\\"vee\\\"];\\n");
		}
		else {
			Analysis.pnfa.println("g.setEdge(" + this.startState.stateName + ", " + this.endState.stateName + ", { label: \"" + this.transSymbol + "\" });");
			//new
			Analysis.pnewnfa.print("    " + this.startState.stateName + " -> " + this.endState.stateName + " [label=\\\"" + this.transSymbol + "\\\" arrowhead = \\\"vee\\\"];\\n");
		}
	}
}

class Cell {
	Set<Edge> edges;
	Set<State> states;//为了方便输出到js文件中
	State startState;
	State endState;
	
	Cell(String TransSymbol) {
		Edge edge = new Edge(TransSymbol);
		this.edges = new HashSet<Edge>();
		this.edges.add(edge);
		this.startState = edge.startState;
		this.endState = edge.endState;
	}
	Cell() {
		this.startState = new State();
		this.endState = new State();
		this.edges = new HashSet<Edge>();
		this.states = new HashSet<State>();
		this.edges.clear();
	}

	public void Print() {
		for(Edge e: edges) {
			e.Print();
		}
		System.out.print("NFA state ");
		startState.Print();
		System.out.println(" is EnterState.");
		System.out.print("NFA state ");
		endState.Print();
		System.out.println(" is ExitState.");
		//new
		Analysis.pnewnfa.print("    " + this.startState.stateName + " [style=\\\"fill: rgb(6, 119, 134)\\\"];\\n");
		Analysis.pnewnfa.print("    " + this.endState.stateName + " [style=\\\"fill: rgb(175, 10, 10)\\\"];\\n");
	}
	
	public void printToJS() {
		for(State s: states) {
			s.printToJS();
		}
		for(Edge e: edges) {
			e.printToJS();
		}
	}
}

/**********************以下类为了NFA2DFA**********************/

class DFA_State {
	static int number = 0;
	String DFAStateName;
	Set<State> states;
	//设置状态是不是入口状态和出口状态
	boolean isEnterState = false;
	boolean isExitState = false;
	
	DFA_State(Set<State> states,Cell NFA) {
		this.DFAStateName = String.valueOf(DFA_State.number);
		DFA_State.number++;
		this.states = states;
		for(State s: this.states) {
			if(s.equals(NFA.startState)) {
				this.isEnterState = true;
			}
			if(s.equals(NFA.endState)) {
				this.isExitState = true;
			}
		}
	}
	
	public void printStatesIn() {
		System.out.print("DFA state " + this.DFAStateName +  " hava the follow states of NFA:");
		for(State s: this.states) {
			System.out.print(" " + s.stateName);
		}
		System.out.print(". ");
		if(this.isEnterState) {
			System.out.print("And this DFA state is a EnterState.");
		}
		if(this.isExitState) {
			System.out.print("And this DFA state is a ExitState.");
		}
		System.out.println();
	}
	
	public void Print() {
		System.out.print(this.DFAStateName);
	}
	
	public void printToJS() {
		Analysis.pdfa.println("g.setNode(" + this.DFAStateName + ", { label: \\\"" + this.DFAStateName + "\\\" });");
		//new
		if(this.isEnterState) {
			Analysis.pnewdfa.print("    " + this.DFAStateName + " [label = \\\"" + this.DFAStateName + "\\\" style=\\\"fill: rgb(6, 119, 134); font-weight: bold\\\" shape= \\\"rect\\\"];\\n");
		} else if(this.isExitState) {
			Analysis.pnewdfa.print("    " + this.DFAStateName + " [label = \\\"" + this.DFAStateName + "\\\" style=\\\"fill: rgb(175, 10, 10); font-weight: bold\\\" shape= \\\"rect\\\"];\\n");
		} else {
			Analysis.pnewdfa.print("    " + this.DFAStateName + " [label = \\\"" + this.DFAStateName + "\\\" shape= \\\"ellipse\\\"];\\n");
		}
	}
}

class DFA_Edge {
	DFA_State startDFAState;
	DFA_State endDFAState;
	String transSymbol;
	
	DFA_Edge(DFA_State startDFAState, DFA_State endDFAState, Character transSymbol) {
		this.startDFAState = startDFAState;
		this.endDFAState = endDFAState;
		this.transSymbol = transSymbol.toString();
	}
	
	public void Print() {
		System.out.print("DFAEdge From:");
		this.startDFAState.Print();
		System.out.print(" To:");
		this.endDFAState.Print();
		System.out.print(" TransSymbol:" + this.transSymbol);
		System.out.print("\n");
	}
	
	public void printToJS() {
		Analysis.pdfa.println("g.setEdge(" + this.startDFAState.DFAStateName + ", " + this.endDFAState.DFAStateName + ", { label: \"" + this.transSymbol + "\" });");
		//new
		Analysis.pnewdfa.print("    " + this.startDFAState.DFAStateName + " -> " + this.endDFAState.DFAStateName + " [label=\\\"" + this.transSymbol + "\\\" arrowhead = \\\"vee\\\"];\\n");
	}
}

class DFA {//里面装了DFA里所有边的集合以及开始状态和终止状态们
	Set<DFA_Edge> DFAEdges;
	Set<DFA_State> DFAStates;
	
	DFA() {
		this.DFAEdges = new HashSet<DFA_Edge>();
		this.DFAStates = new HashSet<DFA_State>();
	}

	public void Print() {
		for(DFA_Edge DFAEdge: this.DFAEdges) {
			DFAEdge.Print();
		}
		for(DFA_State DFAState: this.DFAStates) {
			DFAState.printStatesIn();
		}
	}
	
	public void printToJS() {
		for(DFA_State s: DFAStates) {
			s.printToJS();
		}
		for(DFA_Edge e: DFAEdges) {
			e.printToJS();
		}
	}
}

/**********************以下类为了MinimizeDFA**********************/

class miniDFAState {
	static int number = 0;
	String miniDFAStateName;
	Set<DFA_State> DFAStates;
	//设置状态是不是入口状态和出口状态
	boolean isEnterState = false;
	boolean isExitState = false;

	miniDFAState() {
		this.DFAStates = new HashSet<DFA_State>();
	}
	
	public void set() {
		//Set miniDFAStateName
		this.miniDFAStateName = String.valueOf(miniDFAState.number);
		miniDFAState.number++;
		for(DFA_State DS: DFAStates) {
			this.isEnterState = this.isEnterState||DS.isEnterState;
			this.isExitState = this.isExitState||DS.isExitState;
		}
	}
	
	public void printDFAStatesIn() {
		System.out.print("MiniDFA state " + this.miniDFAStateName +  " hava the follow states of DFA:");
		for(DFA_State DS: this.DFAStates) {
			System.out.print(" " + DS.DFAStateName);
		}
		System.out.print(". ");
		if(this.isEnterState) {
			System.out.print("And this MiniDFA state is a EnterState.");
		}
		if(this.isExitState) {
			System.out.print("And this MiniDFA state is a ExitState.");
		}
		System.out.println();
	}
	
	public void Print() {
		System.out.print(this.miniDFAStateName);
	}
	
	public void printToJS() {
		Analysis.pminidfa.println("g.setNode(" + this.miniDFAStateName + ", { label: \\\"" + this.miniDFAStateName + "\\\" });");
		//new
		if(this.isEnterState) {
			Analysis.pnewminidfa.print("    " + this.miniDFAStateName + " [label = \\\"" + this.miniDFAStateName + "\\\" style=\\\"fill: rgb(6, 119, 134); font-weight: bold\\\" shape= \\\"rect\\\"];\\n");
		} else if(this.isExitState) {
			Analysis.pnewminidfa.print("    " + this.miniDFAStateName + " [label = \\\"" + this.miniDFAStateName + "\\\" style=\\\"fill: rgb(175, 10, 10); font-weight: bold\\\" shape= \\\"rect\\\"];\\n");
		} else {
			Analysis.pnewminidfa.print("    " + this.miniDFAStateName + " [label = \\\"" + this.miniDFAStateName + "\\\" shape= \\\"ellipse\\\"];\\n");
		}
	}
}

class miniDFAEdge {
	miniDFAState startMiniDFAState;
	miniDFAState endMiniDFAState;
	String transSymbol;
	
	miniDFAEdge(miniDFAState startMiniDFAState, miniDFAState endMiniDFAState, String transSymbol) {
		this.startMiniDFAState = startMiniDFAState;
		this.endMiniDFAState = endMiniDFAState;
		this.transSymbol = transSymbol.toString();
	}
	
	public void Print() {
		System.out.print("MiniDFAEdge From:");
		this.startMiniDFAState.Print();
		System.out.print(" To:");
		this.endMiniDFAState.Print();
		System.out.print(" TransSymbol:" + this.transSymbol);
		System.out.print("\n");
	}
	
	public void printToJS() {
		Analysis.pminidfa.println("g.setEdge(" + this.startMiniDFAState.miniDFAStateName + ", " + this.endMiniDFAState.miniDFAStateName + ", { label: \"" + this.transSymbol + "\" });");
		//new
		Analysis.pnewminidfa.print("    " + this.startMiniDFAState.miniDFAStateName + " -> " + this.endMiniDFAState.miniDFAStateName + " [label=\\\"" + this.transSymbol + "\\\" arrowhead = \\\"vee\\\"];\\n");
	}
}

class miniDFA {
	Set<miniDFAState> miniDFAStates;
	Set<miniDFAEdge> miniDFAEdges;
	
	miniDFA() {
		this.miniDFAStates = new HashSet<miniDFAState>();
		this.miniDFAEdges = new HashSet<miniDFAEdge>();
	}
	
	public void Print() {
		for(miniDFAEdge miniDFAEdge: this.miniDFAEdges) {
			miniDFAEdge.Print();
		}
		for(miniDFAState miniDFAState: this.miniDFAStates) {
			miniDFAState.printDFAStatesIn();
		}
	}
	
	public void printToJS() {
		for(miniDFAState s: miniDFAStates) {
			s.printToJS();
		}
		for(miniDFAEdge e: miniDFAEdges) {
			e.printToJS();
		}
	}
}

/**********************以下类为了词法分析程序的生成程序**********************/

class TransferTable {
	String tableName;
	
	String enterState;
	Set<String> acceptableState;
	
	HashMap<String,HashMap<String,String>> lines;
	
	TransferTable() {
		this.lines = new HashMap<String,HashMap<String,String>>();
		this.acceptableState = new HashSet<String>();
	}
}

class Token {
	//type可以是：id、reservedWord、punctuation、number、
	String type;
	
	//str是reservedWord和punctuation的
	String str;
	
	//name是id的
	String name;
	
	//value是number的
	int value;
}