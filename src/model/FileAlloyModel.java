package model;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CompUtil;
import modelrelaxer.ModelRelaxer;
import modelrelaxer.ModelRelaxerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FileAlloyModel implements AlloyModel {

    private String model;
    private Map<String, String> factsMap;
    private Map<String, String> predsMap;
    private Map<String, String> funMap;
    private Map<String, String> assertMap;
    private String onlySigsModel;

    public FileAlloyModel(String filePath) throws IOException {
        StringBuilder modelBuilder = new StringBuilder();
        List<String> lines = Files.readAllLines(Paths.get(filePath));
        String imports = "";
        for (String line: lines) {
            modelBuilder.append(line).append("\n");
            if(line.trim().startsWith("open "))
                imports += line + "\n";
        }
        model = modelBuilder.toString();
        model = model.replaceAll("//.*\n", "");
        model = model.replaceAll("/\\*.*\\*/", "");
        parseFacts();
        parsePreds();
        parseFuncs();
        parseAsserts();
        ModelRelaxerFactory relaxerFactory = new ModelRelaxerFactory();
        ModelRelaxer r = relaxerFactory.createModelRelaxer(CompUtil.parseEverything_fromString(A4Reporter.NOP, model));
        onlySigsModel = imports + r.relaxModel();
        model = onlySigsModel + r.getConstrains();
        for (String fact: factsMap.keySet())
            model += "\nfact " + fact + "{" + factsMap.get(fact) + "}\n";
        for (String pred: predsMap.keySet())
            model += "\npred " + pred + "{" + predsMap.get(pred) + "}\n";
        for (String fun: funMap.keySet())
            model += "\nfun " + fun + "{" + funMap.get(fun) + "}\n";
        for (String assertion: assertMap.keySet())
            model += "\nassert " + assertion + "{" + assertMap.get(assertion) + "}\n";
        parseFacts();
        parsePreds();
        parseFuncs();
        parseAsserts();
    }

    private void parseFacts() {
        factsMap = new HashMap<>();
        int facts = 0;
        Matcher m = Pattern.compile("\\bfact\\b").matcher(model);
        while (m.find()) {
            int i = m.end();
            while (model.charAt(i) != '{')
                i++;
            String name = model.substring(m.end(), i);
            if (name.trim().isEmpty()) {
                name = "fact_" + facts;
                facts++;
            }
            int bodyStart = i+1;
            int curlyBraces = 0;
            do {
                if (model.charAt(i) == '{')
                    curlyBraces++;
                if (model.charAt(i) == '}')
                    curlyBraces--;
                i++;
            }
            while (curlyBraces > 0);
            factsMap.put(name, model.substring(bodyStart, i-1));
        }

    }

    private void parsePreds() {
        predsMap = new HashMap<>();
        Matcher m = Pattern.compile("\\bpred\\b").matcher(model);
        while (m.find()) {
            int i = m.end();
            while (model.charAt(i) != '{')
                i++;
            String name = model.substring(m.end(), i);
            int bodyStart = i+1;
            int curlyBraces = 0;
            do {
                if (model.charAt(i) == '{')
                    curlyBraces++;
                if (model.charAt(i) == '}')
                    curlyBraces--;
                i++;
            }
            while (curlyBraces > 0);
            predsMap.put(name, model.substring(bodyStart, i-1));
        }

    }

    private void parseFuncs() {
        funMap = new HashMap<>();
        Matcher m = Pattern.compile("\\bfun\\b").matcher(model);
        while (m.find()) {
            int i = m.end();
            while (model.charAt(i) != '{')
                i++;
            String name = model.substring(m.end(), i);
            int bodyStart = i+1;
            int curlyBraces = 0;
            do {
                if (model.charAt(i) == '{')
                    curlyBraces++;
                if (model.charAt(i) == '}')
                    curlyBraces--;
                i++;
            }
            while (curlyBraces > 0);
            funMap.put(name, model.substring(bodyStart, i-1));
        }

    }

    private void parseAsserts() {
        assertMap = new HashMap<>();
        int asserts = 0;
        Matcher m = Pattern.compile("\\bassert\\b").matcher(model);
        while (m.find()) {
            int i = m.end();
            while (model.charAt(i) != '{')
                i++;
            String name = model.substring(m.end(), i);
            if (name.trim().isEmpty()) {
                name = "assert_" + asserts;
                asserts++;
            }
            int bodyStart = i+1;
            int curlyBraces = 0;
            do {
                if (model.charAt(i) == '{')
                    curlyBraces++;
                if (model.charAt(i) == '}')
                    curlyBraces--;
                i++;
            }
            while (curlyBraces > 0);
            assertMap.put(name, model.substring(bodyStart, i-1));
        }

    }


    @Override
    public Map<String, String> getPreds() {
        return predsMap;
    }

    @Override
    public Map<String, String> getFacts() {
        return factsMap;
    }

    @Override
    public Map<String, String> getFuns() {
        return funMap;
    }

    @Override
    public Map<String, String> getAsserts() {
        return assertMap;
    }

    @Override
    public String getModel() {
        return model;
    }

    @Override
    public String getOnlySigsModel() {
        return onlySigsModel;
    }

    @Override
    public boolean hasFacts() {
        return !factsMap.isEmpty();
    }

    @Override
    public boolean hasPreds() {
        return !predsMap.isEmpty();
    }

    @Override
    public boolean hasFuns() {
        return !funMap.isEmpty();
    }
}
