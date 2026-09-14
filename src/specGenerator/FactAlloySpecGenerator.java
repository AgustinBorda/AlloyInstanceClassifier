package specGenerator;

import model.AlloyModel;

import java.util.Map;

public class FactAlloySpecGenerator implements AlloySpecGenerator {


    public FactAlloySpecGenerator() {
    }


    @Override
    public String generateModelForClassification(AlloyModel correct, AlloyModel buggy, int scope) {
        String result = buggy.getOnlySigsModel();
        for (Map.Entry<String, String> pred: buggy.getPreds().entrySet()) {
            result += "pred " + pred.getKey().trim() + " {" + pred.getValue() + "}\n";
        }
        for (Map.Entry<String, String> fun: buggy.getFuns().entrySet()) {
            result += "fun " + fun.getKey().trim() + " {" + fun.getValue() + "}\n";
        }
        for (Map.Entry<String, String> fact: buggy.getFacts().entrySet()) {
            result += "pred " + fact.getKey().trim() + " {" + fact.getValue() + "}\n";
        }
        for (Map.Entry<String, String> fact: correct.getFacts().entrySet()) {
            result += "pred " + fact.getKey().trim() + "_correct {" + fact.getValue() + "}\n";
        }
        String template = "";
        for (String fact: buggy.getFacts().keySet()) {
            template += fact.trim() + "[] and " + fact.trim() + "_correct[] and ";
        }
        template = template.substring(0, template.length()-4);
        String overSpec = "pred overspecification {\n";
        String underSpec = "pred underspecification {\n";
        for (String fact: buggy.getFacts().keySet()) {
            underSpec +=  "(" + template.replaceAll(fact.trim() + "_correct\\[]", "not " + fact.trim() + "_correct[]") + ") or\n";
            overSpec +=  "(" + template.replaceAll(fact.trim() + "\\[]", "not " + fact.trim() + "[]") + ") or\n";
        }
        overSpec = overSpec.substring(0,overSpec.length()-4);
        underSpec = underSpec.substring(0,underSpec.length()-4);
        overSpec +="\n}\n";
        underSpec +="\n}\n";
        result += overSpec + underSpec;
        result += "run overspecification for " + scope + "\n";
        result += "run underspecification for " + scope + "\n";
        return result;
    }
}
