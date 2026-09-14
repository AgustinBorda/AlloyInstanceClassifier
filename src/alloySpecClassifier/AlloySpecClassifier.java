package alloySpecClassifier;

import model.AlloyModel;

import java.io.IOException;

public interface AlloySpecClassifier {

    void classifyBuggySpecs(String oraclePath, String buggyModelsPath, int scope) throws IOException;

}
