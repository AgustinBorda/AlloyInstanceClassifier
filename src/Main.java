

import alloySpecClassifier.AlloySpecClassifier;
import alloySpecClassifier.SimpleAlloySpecClassifier;

import java.io.IOException;

public class Main {
    public static void main(String[] args) throws IOException {
        AlloySpecClassifier classifier = new SimpleAlloySpecClassifier();
        classifier.classifyBuggySpecs(args[0], args[1], Integer.parseInt(args[2]));
    }


}