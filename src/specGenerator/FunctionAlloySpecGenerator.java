package specGenerator;

import model.AlloyModel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class FunctionAlloySpecGenerator implements AlloySpecGenerator {


    public FunctionAlloySpecGenerator() {
    }


    @Override
    public String generateModelForClassification(AlloyModel correct, AlloyModel buggy, int scope) {
        String result = buggy.getModel();
        for (Map.Entry<String, String> fun: correct.getFuns().entrySet()) {
            result += "fun " + fun.getKey().trim().replaceAll("( ?)\\[", "_correct[") + " {" + fun.getValue().trim() + "}\n";
        }
        String error = "pred error {\n";
        for (String pred: correct.getFuns().keySet()) {
            error += calculateInvocationString(pred) + " or\n";
        }
        error = error.substring(0,error.length()-4);
        error +="\n}\n";
        result += error;
        result += "run error for " + scope + "\n";
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
        return "(" + prefix + name + "[" + actualParams + "] != " + name +"_correct[" + actualParams + "])";
    }

}
