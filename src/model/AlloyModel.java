package model;

import java.util.Map;

public interface AlloyModel {

    Map<String, String> getPreds();
    Map<String, String> getFacts();
    Map<String, String> getFuns();
    Map<String, String> getAsserts();
    String getModel();
    String getOnlySigsModel();
    boolean hasFacts();
    boolean hasPreds();
    boolean hasFuns();

}
