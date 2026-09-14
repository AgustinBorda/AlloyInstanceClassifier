package specGenerator;

import model.AlloyModel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class PredicateAlloySpecGenerator implements AlloySpecGenerator {


    public PredicateAlloySpecGenerator() {
    }


    @Override
    public String generateModelForClassification(AlloyModel correct, AlloyModel buggy, int scope) {
        String result = buggy.getModel();
        for (Map.Entry<String, String> predicate: correct.getPreds().entrySet()) {
            if(predicate.getKey().trim().contains("["))
                result += "pred " + predicate.getKey().trim().replaceAll("( ?)\\[", "_correct[") + " {" + predicate.getValue().trim() + "}\n";
            else
                result += "pred " + predicate.getKey().trim() + "_correct {" + predicate.getValue().trim() + "}\n";
        }
        String overSpec = "pred overspecification {\n";
        String underSpec = "pred underspecification {\n";
        for (String pred: correct.getPreds().keySet()) {
            String predName = pred.trim().split("\\[")[0].trim();
            String template = calculateInvocationString(pred);
            underSpec += template.replaceAll(predName + "_correct\\[", "not " + predName + "_correct[")+ " or\n";
            overSpec += template.replaceAll(predName + "\\[", "not " + predName + "[")+ " or\n";
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


    private String calculateInvocationString(String pred) {
        List<String> types = new ArrayList<>();
        List<String> vars = new ArrayList<>();
        String rawPred = pred.trim();
        String[] predAndParams = rawPred.split("\\[");
        String name = predAndParams[0].trim();
        if (predAndParams.length > 1) {
            String params = predAndParams[1].split("]")[0];
            String[] splitParams = params.split(":( *)[a-zA-z0-9]+(,?)");
            for (int i = 0; i< splitParams.length; i++) {
                vars.add(splitParams[i].trim());
            }

            String[] paramsAndTypes = params.split(",");
            for (String values: paramsAndTypes) {
                if (values.contains(":")) {
                    String[] splitValues = values.split(":");
                    types.add(splitValues[1].trim());
                }
            }
        }
        String prefix = "";
        String actualParams = "";
        for (int i = 0; i < types.size(); i++) {
            prefix += "some " + vars.get(i) + ": " + types.get(i) + " | ";
            actualParams += vars.get(i) + ", ";
        }
        if(!actualParams.isEmpty())
            actualParams = actualParams.substring(0,actualParams.length()-2);
        return "(" + prefix + name + "[" + actualParams + "] and " + name +"_correct[" + actualParams + "])";
    }

}
