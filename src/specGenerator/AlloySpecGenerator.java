package specGenerator;

import model.AlloyModel;

public interface AlloySpecGenerator {
    String generateModelForClassification(AlloyModel correct, AlloyModel buggy, int scope);
}
