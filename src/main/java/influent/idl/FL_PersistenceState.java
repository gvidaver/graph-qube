/**
 * Autogenerated by Avro
 * 
 * DO NOT EDIT DIRECTLY
 */
package influent.idl;  
@SuppressWarnings("all")
/** Persistence save state */
@org.apache.avro.specific.AvroGenerated
public enum FL_PersistenceState { 
  NEW, MODIFIED, NONE, ERROR  ;
  public static final org.apache.avro.Schema SCHEMA$ = new org.apache.avro.Schema.Parser().parse("{\"type\":\"enum\",\"name\":\"FL_PersistenceState\",\"namespace\":\"influent.idl\",\"doc\":\"Persistence save state\",\"symbols\":[\"NEW\",\"MODIFIED\",\"NONE\",\"ERROR\"]}");
  public static org.apache.avro.Schema getClassSchema() { return SCHEMA$; }
}
