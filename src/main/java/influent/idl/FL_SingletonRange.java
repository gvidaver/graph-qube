/**
 * Autogenerated by Avro
 * 
 * DO NOT EDIT DIRECTLY
 */
package influent.idl;  
@SuppressWarnings("all")
/** Single value
	
	ADDED IN 1.5 */
@org.apache.avro.specific.AvroGenerated
public class FL_SingletonRange extends org.apache.avro.specific.SpecificRecordBase implements org.apache.avro.specific.SpecificRecord {
  public static final org.apache.avro.Schema SCHEMA$ = new org.apache.avro.Schema.Parser().parse("{\"type\":\"record\",\"name\":\"FL_SingletonRange\",\"namespace\":\"influent.idl\",\"doc\":\"Single value\\r\\n\\t\\r\\n\\tADDED IN 1.5\",\"fields\":[{\"name\":\"value\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"int\",\"float\",\"double\",\"long\",\"boolean\",{\"type\":\"record\",\"name\":\"FL_GeoData\",\"doc\":\"Structured representation of geo-spatial data.\",\"fields\":[{\"name\":\"text\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"null\"],\"doc\":\"an address or other place reference; unstructured text field\",\"default\":null},{\"name\":\"lat\",\"type\":[\"double\",\"null\"],\"doc\":\"latitude\",\"default\":null},{\"name\":\"lon\",\"type\":[\"double\",\"null\"],\"doc\":\"longitude\",\"default\":null},{\"name\":\"cc\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"null\"],\"doc\":\"ISO 3 digit country code\",\"default\":null}]}]},{\"name\":\"type\",\"type\":{\"type\":\"enum\",\"name\":\"FL_PropertyType\",\"doc\":\"Allowed types for Property values.\\r\\n\\r\\n\\t CHANGED in 1.5\",\"symbols\":[\"DOUBLE\",\"LONG\",\"BOOLEAN\",\"STRING\",\"DATE\",\"GEO\",\"OTHER\"]},\"doc\":\"One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER\"}]}");
  public static org.apache.avro.Schema getClassSchema() { return SCHEMA$; }
   private java.lang.Object value;
  /** One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER */
   private influent.idl.FL_PropertyType type;

  /**
   * Default constructor.
   */
  public FL_SingletonRange() {}

  /**
   * All-args constructor.
   */
  public FL_SingletonRange(java.lang.Object value, influent.idl.FL_PropertyType type) {
    this.value = value;
    this.type = type;
  }

  public org.apache.avro.Schema getSchema() { return SCHEMA$; }
  // Used by DatumWriter.  Applications should not call. 
  public java.lang.Object get(int field$) {
    switch (field$) {
    case 0: return value;
    case 1: return type;
    default: throw new org.apache.avro.AvroRuntimeException("Bad index");
    }
  }
  // Used by DatumReader.  Applications should not call. 
  @SuppressWarnings(value="unchecked")
  public void put(int field$, java.lang.Object value$) {
    switch (field$) {
    case 0: value = (java.lang.Object)value$; break;
    case 1: type = (influent.idl.FL_PropertyType)value$; break;
    default: throw new org.apache.avro.AvroRuntimeException("Bad index");
    }
  }

  /**
   * Gets the value of the 'value' field.
   */
  public java.lang.Object getValue() {
    return value;
  }

  /**
   * Sets the value of the 'value' field.
   * @param value the value to set.
   */
  public void setValue(java.lang.Object value) {
    this.value = value;
  }

  /**
   * Gets the value of the 'type' field.
   * One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER   */
  public influent.idl.FL_PropertyType getType() {
    return type;
  }

  /**
   * Sets the value of the 'type' field.
   * One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER   * @param value the value to set.
   */
  public void setType(influent.idl.FL_PropertyType value) {
    this.type = value;
  }

  /** Creates a new FL_SingletonRange RecordBuilder */
  public static influent.idl.FL_SingletonRange.Builder newBuilder() {
    return new influent.idl.FL_SingletonRange.Builder();
  }
  
  /** Creates a new FL_SingletonRange RecordBuilder by copying an existing Builder */
  public static influent.idl.FL_SingletonRange.Builder newBuilder(influent.idl.FL_SingletonRange.Builder other) {
    return new influent.idl.FL_SingletonRange.Builder(other);
  }
  
  /** Creates a new FL_SingletonRange RecordBuilder by copying an existing FL_SingletonRange instance */
  public static influent.idl.FL_SingletonRange.Builder newBuilder(influent.idl.FL_SingletonRange other) {
    return new influent.idl.FL_SingletonRange.Builder(other);
  }
  
  /**
   * RecordBuilder for FL_SingletonRange instances.
   */
  public static class Builder extends org.apache.avro.specific.SpecificRecordBuilderBase<FL_SingletonRange>
    implements org.apache.avro.data.RecordBuilder<FL_SingletonRange> {

    private java.lang.Object value;
    private influent.idl.FL_PropertyType type;

    /** Creates a new Builder */
    private Builder() {
      super(influent.idl.FL_SingletonRange.SCHEMA$);
    }
    
    /** Creates a Builder by copying an existing Builder */
    private Builder(influent.idl.FL_SingletonRange.Builder other) {
      super(other);
    }
    
    /** Creates a Builder by copying an existing FL_SingletonRange instance */
    private Builder(influent.idl.FL_SingletonRange other) {
            super(influent.idl.FL_SingletonRange.SCHEMA$);
      if (isValidValue(fields()[0], other.value)) {
        this.value = data().deepCopy(fields()[0].schema(), other.value);
        fieldSetFlags()[0] = true;
      }
      if (isValidValue(fields()[1], other.type)) {
        this.type = data().deepCopy(fields()[1].schema(), other.type);
        fieldSetFlags()[1] = true;
      }
    }

    /** Gets the value of the 'value' field */
    public java.lang.Object getValue() {
      return value;
    }
    
    /** Sets the value of the 'value' field */
    public influent.idl.FL_SingletonRange.Builder setValue(java.lang.Object value) {
      validate(fields()[0], value);
      this.value = value;
      fieldSetFlags()[0] = true;
      return this; 
    }
    
    /** Checks whether the 'value' field has been set */
    public boolean hasValue() {
      return fieldSetFlags()[0];
    }
    
    /** Clears the value of the 'value' field */
    public influent.idl.FL_SingletonRange.Builder clearValue() {
      value = null;
      fieldSetFlags()[0] = false;
      return this;
    }

    /** Gets the value of the 'type' field */
    public influent.idl.FL_PropertyType getType() {
      return type;
    }
    
    /** Sets the value of the 'type' field */
    public influent.idl.FL_SingletonRange.Builder setType(influent.idl.FL_PropertyType value) {
      validate(fields()[1], value);
      this.type = value;
      fieldSetFlags()[1] = true;
      return this; 
    }
    
    /** Checks whether the 'type' field has been set */
    public boolean hasType() {
      return fieldSetFlags()[1];
    }
    
    /** Clears the value of the 'type' field */
    public influent.idl.FL_SingletonRange.Builder clearType() {
      type = null;
      fieldSetFlags()[1] = false;
      return this;
    }

    @Override
    public FL_SingletonRange build() {
      try {
        FL_SingletonRange record = new FL_SingletonRange();
        record.value = fieldSetFlags()[0] ? this.value : (java.lang.Object) defaultValue(fields()[0]);
        record.type = fieldSetFlags()[1] ? this.type : (influent.idl.FL_PropertyType) defaultValue(fields()[1]);
        return record;
      } catch (Exception e) {
        throw new org.apache.avro.AvroRuntimeException(e);
      }
    }
  }
}
