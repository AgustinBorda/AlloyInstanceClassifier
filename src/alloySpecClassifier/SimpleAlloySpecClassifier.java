package alloySpecClassifier;

import alloyRunner.AlloyRunner;
import alloyRunner.SimpleAlloyRunner;
import model.AlloyModel;
import model.FileAlloyModel;
import specGenerator.AlloySpecGenerator;
import specGenerator.FactAlloySpecGenerator;
import specGenerator.FunctionAlloySpecGenerator;
import specGenerator.PredicateAlloySpecGenerator;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Objects;

public class SimpleAlloySpecClassifier implements AlloySpecClassifier {

    private AlloySpecGenerator factGenerator;
    private AlloySpecGenerator funGenerator;
    private AlloySpecGenerator predGenerator;
    private AlloyRunner runner;

    public SimpleAlloySpecClassifier() {
        factGenerator = new FactAlloySpecGenerator();
        funGenerator = new FunctionAlloySpecGenerator();
        predGenerator = new PredicateAlloySpecGenerator();
        runner = new SimpleAlloyRunner();
    }

    @Override
    public void classifyBuggySpecs(String oraclePath, String buggyModelsPath, int scope) throws IOException {
        AlloyModel correctModel = new FileAlloyModel(oraclePath);
        File dir = new File(buggyModelsPath);
        File hardSpecs = new File(buggyModelsPath + "/hard");
        hardSpecs.mkdir();
        long totalInstances = 0;
        int models = 0;
        File[] childs = Objects.requireNonNull(dir.listFiles());
        for (File child: childs) {
            if(child.isDirectory())
                continue;
            int instances = 0;
            AlloyModel buggyModel = new FileAlloyModel(child.getPath());
            if (correctModel.hasFacts()) {
                instances += runner.runModelAndReturnInstanceQuantity(factGenerator.generateModelForClassification(correctModel, buggyModel, scope));
            }
            if (correctModel.hasPreds()) {
                instances += runner.runModelAndReturnInstanceQuantity(predGenerator.generateModelForClassification(correctModel, buggyModel, scope));
            }
            if (correctModel.hasFuns()) {
                instances += runner.runModelAndReturnInstanceQuantity(funGenerator.generateModelForClassification(correctModel, buggyModel, scope));
            }
            System.out.println((models+1) + "/" + childs.length + " The model " + child.getName() + (instances == 10000 ? " has >=": " has ") + instances + " bug-revealing instances.");
            totalInstances += instances;
            models++;
            if(instances < 10000)
                Files.copy(Paths.get(child.getAbsolutePath()), Paths.get(hardSpecs.getAbsolutePath() + "/" + child.getName()));
        }
        System.out.println("Average " + totalInstances/models);
    }
}
