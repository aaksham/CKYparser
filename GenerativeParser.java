package edu.berkeley.nlp.assignments.parsing.student;

import edu.berkeley.nlp.assignments.parsing.*;
import edu.berkeley.nlp.ling.Tree;
import edu.berkeley.nlp.ling.Trees;
import edu.berkeley.nlp.util.Indexer;

import java.util.*;

public class GenerativeParser implements Parser {
    SimpleLexicon lexicon;
    Grammar grammar;
    UnaryClosure unary_closure;
    static int hint=2;
    static int v=2;
    static String h="2";
    public GenerativeParser(List<Tree<String>> trainTrees) {
        System.out.print("Annotating / binarizing training trees ... ");
        if(h!="inf"){hint=Integer.parseInt(h);}
        List annotatedTrainTrees = this.annotateTrees(trainTrees);
        System.out.println("done.");
        System.out.print("Building grammar ... ");
        this.grammar = Grammar.generativeGrammarFromTrees(annotatedTrainTrees);
        System.out.println("done. (" + grammar.getLabelIndexer().size() + " states)" +grammar.getBinaryRules().size()+","+grammar.getUnaryRules().size()+" rules");
        System.out.print("Calculating unary closure ... ");
        List unaries=grammar.getUnaryRules();
        this.unary_closure=new UnaryClosure(grammar.getLabelIndexer(),unaries);
        this.lexicon = new SimpleLexicon(annotatedTrainTrees);
        System.out.println("done.");
    }
    public Tree<String> getBestParse(List<String> sentence) {
        Tree annotatedBestParse = getCYKparse(sentence);
        return TreeAnnotations.unAnnotateTree(annotatedBestParse);
    }
    public Tree<String> getCYKparse(List<String> sentence){
        Indexer gIndexer=grammar.getLabelIndexer();
        int length=sentence.size();
        Map<String, Double>[][] scoreChart=(HashMap<String, Double>[][]) new HashMap[length+1][length+1];
        Map<String,GenerativeParser.Backtrace>[][] backtracker=(HashMap<String,GenerativeParser.Backtrace>[][]) new HashMap[length+1][length+1];
        for (int j = 1; j <= length; j++) {
            scoreChart[j - 1][j] = new HashMap<String, Double>();
            backtracker[j - 1][j] = new HashMap<String, GenerativeParser.Backtrace>();
            Iterator tagIterator=lexicon.getAllTags().iterator();
            while (tagIterator.hasNext()) {
                String tag=(String)tagIterator.next();
                double score = lexicon.scoreTagging(sentence.get(j - 1), tag);
                if (score == Double.NEGATIVE_INFINITY) continue;
                scoreChart[j - 1][j].put(tag, score);
                int tagIndex=gIndexer.indexOf(tag);
                List<UnaryRule> unary_rules = this.unary_closure.getClosedUnaryRulesByChild(tagIndex);
                Iterator unary_rule_iterator=unary_rules.iterator();
                while(unary_rule_iterator.hasNext()){
                    UnaryRule ur=(UnaryRule)unary_rule_iterator.next();
                    int parent=ur.getParent();
                    if (parent==tagIndex) continue;
                    String parentLabel=(String)gIndexer.get(parent);
                    Double oldscore=scoreChart[j-1][j].get(parentLabel);
                    Double newscore=score+ur.getScore();
                    if(oldscore==null||oldscore<newscore){
                        scoreChart[j-1][j].put(parentLabel,newscore);
                        backtracker[j-1][j].put(parentLabel, GenerativeParser.Backtrace.addUnaryBacktrace(ur));
                    }
                }
            }
            for(int i=j-2;i>=0;i--){
                scoreChart[i][j]=new HashMap<String,Double>();
                backtracker[i][j]=new HashMap<String, GenerativeParser.Backtrace>();
                for(int k=i+1;k<j;k++){
                    Map<String,Double> rightChildStates= scoreChart[k][j];
                    Set leftChildStateLabels=scoreChart[i][k].keySet();
                    Iterator leftChildIterator=leftChildStateLabels.iterator();
                    while (leftChildIterator.hasNext()){
                        String blabel=(String)leftChildIterator.next();
                        int B=gIndexer.indexOf(blabel);
                        List brs=grammar.getBinaryRulesByLeftChild(B);
                        Iterator brs_iterator=brs.iterator();
                        while(brs_iterator.hasNext()){
                            BinaryRule br=(BinaryRule)brs_iterator.next();
                            int C=br.getRightChild();
                            String clabel=(String)gIndexer.get(C);
                            if(rightChildStates.containsKey(clabel)){
                                int A=br.getParent();
                                String alabel=(String)gIndexer.get(A);
                                double newscore=scoreChart[i][k].get(blabel)+rightChildStates.get(clabel)+br.getScore();
                                Double oldscore=scoreChart[i][j].get(alabel);
                                if(oldscore==null||oldscore<newscore){
                                    scoreChart[i][j].put(alabel,newscore);
                                    backtracker[i][j].put(alabel, GenerativeParser.Backtrace.addBinaryBacktrace(k,blabel,clabel));
                                }
                            }
                        }
                    }
                }
                Set parentStateLabels=scoreChart[i][j].keySet();
                ArrayList list_of_keys=new ArrayList();
                list_of_keys.addAll(parentStateLabels);
                Iterator parentIterator=list_of_keys.iterator();
                while(parentIterator.hasNext()){
                    String alabel=(String)parentIterator.next();
                    int A=gIndexer.indexOf(alabel);
                    List<UnaryRule> unary_rules = this.unary_closure.getClosedUnaryRulesByChild(A);
                    Double score_of_a=scoreChart[i][j].get(alabel);
                    Iterator unary_rule_iterator=unary_rules.iterator();
                    while(unary_rule_iterator.hasNext()){
                        UnaryRule ur=(UnaryRule)unary_rule_iterator.next();
                        int parent=ur.getParent();
                        if (parent==A) continue;
                        String parentLabel=(String)gIndexer.get(parent);
                        Double oldscore=scoreChart[i][j].get(parentLabel);
                        double newscore=score_of_a+ur.getScore();
                        if(oldscore==null||oldscore<newscore){
                            scoreChart[i][j].put(parentLabel,newscore);
                            backtracker[i][j].put(parentLabel, GenerativeParser.Backtrace.addUnaryBacktrace(ur));
                        }
                    }
                }
            }
        }
        if(v==2) return makeTree(sentence,0,length,"ROOT^ROOT",backtracker);
        return makeTree(sentence,0,length,"ROOT",backtracker);
    }
    private Tree<String> makeTree(List<String> sentence, int i, int length, String root, Map<String, GenerativeParser.Backtrace>[][] backtracker) {
        if (i==length-1){
            GenerativeParser.Backtrace trace= backtracker[i][length].get(root);
            if(trace==null){return new Tree<String>(root,Collections.singletonList(new Tree<String>(sentence.get(i))));}
            List path=this.unary_closure.getPath(trace.unaryRule);
            List placeholder=Collections.emptyList();
            Tree leaf=new Tree(sentence.get(i),placeholder);
            return makeUnaryTree(path,Collections.singletonList(leaf));
        }
        Indexer gIndexer=grammar.getLabelIndexer();
        GenerativeParser.Backtrace trace=backtracker[i][length].get(root);
        if(trace.is_a_unaryRule()){
            UnaryRule ur=trace.unaryRule;
            String next= (String) gIndexer.get(ur.getChild());
            Tree leaf=makeTree(sentence,i,length,next,backtracker);
            List path=this.unary_closure.getPath(ur);
            return makeUnaryTree(path.subList(0,path.size()-1),Collections.singletonList(leaf));
        }
        Tree leftTree=makeTree(sentence,i,trace.k,trace.B,backtracker);
        Tree rightTree=makeTree(sentence,trace.k,length,trace.C,backtracker);
        ArrayList<Tree<String>> children = new ArrayList<Tree<String>>(2);
        children.add(leftTree);
        children.add(rightTree);
        return new Tree(root,children);
    }

    private Tree<String> makeUnaryTree(List path, List<Tree> leaf) {
        List finaltree=leaf;
        Indexer gIndexer=grammar.getLabelIndexer();
        for(int i=path.size()-1;i>=0;i--) {
            String newlabel=(String)gIndexer.get((int)path.get(i));
            finaltree = Collections.singletonList(new Tree(newlabel, finaltree));
        }
        return (Tree)finaltree.get(0);
    }

    private List<Tree<String>> annotateTrees(List<Tree<String>> trees) {
        ArrayList annotatedTrees = new ArrayList();
        Iterator var3 = trees.iterator();

        while(var3.hasNext()) {
            Tree tree = (Tree)var3.next();
            if(h=="inf" && v==1) annotatedTrees.add(TreeAnnotations.annotateTreeLosslessBinarization(tree));
            else annotatedTrees.add(annotateTreeMarkovBinarization(tree));
        }

        return annotatedTrees;
    }
    private Tree<String> annotateTreeMarkovBinarization(Tree tree) {
        return markovBinarizeTree(tree, "ROOT");
    }
    private static Tree<String> markovBinarizeTree(Tree tree, String parent){
        String label=(String)tree.getLabel();
        String newlabel=new String();
        if(v==2) newlabel= new String(label+"^"+parent);
        else if (v==1) newlabel=label;
        if(tree.isLeaf()) return new Tree<String>(label);
        if(tree.getChildren().size()==1){
            return new Tree(newlabel, Collections.singletonList(markovBinarizeTree((Tree)tree.getChildren().get(0),label)));
        }
        Tree tempTree=markovBinarizeTreeHelper(tree,tree.getChildren().size()-1,newlabel,label);
        return new Tree(newlabel,tempTree.getChildren());
    }
    private static Tree markovBinarizeTreeHelper(Tree<String> tree, int childnumber,String newlabel,String nextparent) {
        Tree rightTree=markovBinarizeTree((Tree)tree.getChildren().get(childnumber),nextparent);
        List children=new ArrayList();
        if(childnumber>0){
            Tree leftTree=markovBinarizeTreeHelper(tree,childnumber-1,newlabel,nextparent);
            children.add(leftTree);
            children.add(rightTree);
        }
        else{
            return rightTree;
        }
        StringBuilder headlabel=new StringBuilder();
        int horizontalHistory=childnumber+1-hint;
        int start=0;
        if(horizontalHistory>0) start=horizontalHistory;
        for(int i=start;i<=childnumber;i++){
            String label_to_add=tree.getChildren().get(i).getLabel();
            headlabel.append(new String("_"+label_to_add));
        }
        String final_headlabel=new String("@"+newlabel+"->.."+headlabel.toString());
        return new Tree<String>(final_headlabel,children);
    }
    public static class Backtrace{
        public int k;
        public String B,C;
        public UnaryRule unaryRule;

        public static GenerativeParser.Backtrace addBinaryBacktrace(int k, String b, String c){return new GenerativeParser.Backtrace(k,b,c);}
        public static GenerativeParser.Backtrace addUnaryBacktrace(UnaryRule unaryRule){return new GenerativeParser.Backtrace(unaryRule);}
        private Backtrace(int k,String b, String c){this.k=k;this.B=b;this.C=c;}
        private Backtrace(UnaryRule unaryRule){this.unaryRule=unaryRule;}
        public boolean is_a_unaryRule(){
            return unaryRule!=null;
        }
    }

}

