/**
 * Autogenerated by Avro
 * 
 * DO NOT EDIT DIRECTLY
 */
package influent.idl;  
@SuppressWarnings("all")
/** Bounded or unbounded range values
	
	ADDED IN 1.5 */
@org.apache.avro.specific.AvroGenerated
public class FL_BoundedRange extends org.apache.avro.specific.SpecificRecordBase implements org.apache.avro.specific.SpecificRecord {
  public static final org.apache.avro.Schema SCHEMA$ = new org.apache.avro.Schema.Parser().parse("{\"type\":\"record\",\"name\":\"FL_BoundedRange\",\"namespace\":\"influent.idl\",\"doc\":\"Bounded or unbounded range values\\r\\n\\t\\r\\n\\tADDED IN 1.5\",\"fields\":[{\"name\":\"start\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"int\",\"float\",\"double\",\"long\",\"boolean\",{\"type\":\"record\",\"name\":\"FL_GeoData\",\"doc\":\"Structured representation of geo-spatial data.\",\"fields\":[{\"name\":\"text\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"null\"],\"doc\":\"an address or other place reference; unstructured text field\",\"default\":null},{\"name\":\"lat\",\"type\":[\"double\",\"null\"],\"doc\":\"latitude\",\"default\":null},{\"name\":\"lon\",\"type\":[\"double\",\"null\"],\"doc\":\"longitude\",\"default\":null},{\"name\":\"cc\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"null\"],\"doc\":\"ISO 3 digit country code\",\"default\":null}]},\"null\"],\"doc\":\"start of range, or null if unbounded start\"},{\"name\":\"end\",\"type\":[{\"type\":\"string\",\"avro.java.string\":\"String\"},\"int\",\"float\",\"double\",\"long\",\"boolean\",\"FL_GeoData\",\"null\"],\"doc\":\"end of range, or null if unbounded start\"},{\"name\":\"inclusive\",\"type\":\"boolean\",\"doc\":\"If true, range includes specified endpoint. If false, range is exclusive.\"},{\"name\":\"type\",\"type\":{\"type\":\"enum\",\"name\":\"FL_PropertyType\",\"doc\":\"Allowed types for Property values.\\r\\n\\r\\n\\t CHANGED in 1.5\",\"symbols\":[\"DOUBLE\",\"LONG\",\"BOOLEAN\",\"STRING\",\"DATE\",\"GEO\",\"OTHER\"]},\"doc\":\"One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER\"}]}");
  public static org.apache.avro.Schema getClassSchema() { return SCHEMA$; }
  /** start of range, or null if unbounded start */
   private java.lang.Object start;
  /** end of range, or null if unbounded start */
   private java.lang.Object end;
  /** If true, range includes specified endpoint. If false, range is exclusive. */
   private boolean inclusive;
  /** One of DOUBLE, LONG, BOOLEAN, STRING, DATE, GEO, OTHER */
   private influent.idl.FL_PropertyType type;

  /**
   * Default constructor.
   */
  public FL_BoundedRange() {}

  /**
   * All-args constructor.
   */
  public FL_BoundedRange(java.lang.Object start, java.lang.Object end, java.lang.Boolean inclusive, influent.idl.FL_PropertyType type) {
    this.start = start;
    this.end = end;
    this.inclusive = inclusive;
    this.type = type;
  }

  public org.apache.avro.Schema getSchema() { return SCHEMA$; }
  // Used by DatumWriter.  Applications should not call. 
  public java.lang.Object get(int field$) {
    switch (field$) {
    case 0: return start;
    case 1: return end;
    case 2: return inclusive;
    case 3: return type;
    default: throw new org.apache.avro.AvroRuntimeException("Bad index");
    }
  }
  // Used by DatumReader.  Applications should not call. 
  @SuppressWarnings(value="unchecked")
  public void put(int field$, java.lang.Object value$) {
    switch (field$) {
    case 0: start = (java.lang.Object)value$; break;
    case 1: end = (java.lang.Object)value$; break;
    case 2: inclusive = (java.lang.Boolean)value$; break;
    case 3: type = (influent.idl.FL_PropertyType)value$; break;
    default: throw new org.apache.avro.AvroRuntimeException("Bad index");
    }
  }

  /**
   * Gets the value of the 'start' field.
   * start of range, or null if unbounded start   */
  public java.lang.Object getStart() {
    return start;
  }

  /**
   * Sets the value of the 'start' field.
   * start of range, or null if unbounded start   * @param value the value to set.
   */
  public void setStart(java.lang.Object value) {
    this.start = value;
  }

  /**
   * Gets the value of the 'end' field.
   * end of range, or null if unbounded start   */
  public java.lang.Object getEnd() {
    return end;
  }

  /**
   * Sets the value of the 'end' field.
   * end of range, or null if unbounded start   * @param value the value to set.
   */
  public void setEnd(java.lang.Object value) {
    this.end = value;
  }

  /**
   * Gets the value of the 'inclusive' field.
   * If true, range includes specified endpoint. If false, range is exclusive.   */
  public java.lang.Boolean getInclusive() {
    return inclusive;
  }

  /**
   * Sets the value of the 'inclusive' field.
   * If true, range includes specified endpoint. If false, range is exclusive.   * @param value the value to set.
   */
  public void setInclusive(java.lang.Boolean value) {
    this.inclusive = value;
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

  /** Creates a new FL_BoundedRange RecordBuilder */
  public static influent.idl.FL_BoundedRange.Builder newBuilder() {
    return new influent.idl.FL_BoundedRange.Builder();
  }
  
  /** Creates a new FL_BoundedRange RecordBuilder by copying an existing Builder */
  public static influent.idl.FL_BoundedRange.Builder newBuilder(influent.idl.FL_BoundedRange.Builder other) {
    return new influent.idl.FL_BoundedRange.Builder(other);
  }
  
  /** Creates a new FL_BoundedRange RecordBuilder by copying an existing FL_BoundedRange instance */
  public static influent.idl.FL_BoundedRange.Builder newBuilder(influent.idl.FL_BoundedRange other) {
    return new influent.idl.FL_BoundedRange.Builder(other);
  }
  
  /**
   * RecordBuilder for FL_BoundedRange instances.
   */
  public static class Builder extends org.apache.avro.specific.SpecificRecordBuilderBase<FL_BoundedRange>
    implements org.apache.avro.data.RecordBuilder<FL_BoundedRange> {

    private java.lang.Object start;
    private java.lang.Object end;
    private boolean inclusive;
    private influent.idl.FL_PropertyType type;

    /** Creates a new Builder */
    private Builder() {
      super(influent.idl.FL_BoundedRange.SCHEMA$);
    }
    
    /** Creates a Builder by copying an existing Builder */
    private Builder(influent.idl.FL_BoundedRange.Builder other) {
      super(other);
    }
    
    /** Creates a Builder by copying an existing FL_BoundedRange instance */
    private Builder(influent.idl.FL_BoundedRange other) {
            super(influent.idl.FL_BoundedRange.SCHEMA$);
      if (isValidValue(fields()[0], other.start)) {
        this.start = data().deepCopy(fields()[0].schema(), other.start);
        fieldSetFlags()[0] = true;
      }
      if (isValidValue(fields()[1], other.end)) {
        this.end = data().deepCopy(fields()[1].schema(), other.end);
        fieldSetFlags()[1] = true;
      }
      if (isValidValue(fields()[2], other.inclusive)) {
        this.inclusive = data().deepCopy(fields()[2].schema(), other.inclusive);
        fieldSetFlags()[2] = true;
      }
      if (isValidValue(fields()[3], other.type)) {
        this.type = data().deepCopy(fields()[3].schema(), other.type);
        fieldSetFlags()[3] = true;
      }
    }

    /** Gets the value of the 'start' field */
    public java.lang.Object getStart() {
      return start;
    }
    
    /** Sets the value of the 'start' field */
    public influent.idl.FL_BoundedRange.Builder setStart(java.lang.Object value) {
      validate(fields()[0], value);
      this.start = value;
      fieldSetFlags()[0] = true;
      return this; 
    }
    
    /** Checks whether the 'start' field has been set */
    public boolean hasStart() {
      return fieldSetFlags()[0];
    }
    
    /** Clears the value of the 'start' field */
    public influent.idl.FL_BoundedRange.Builder clearStart() {
      start = null;
      fieldSetFlags()[0] = false;
      return this;
    }

    /** Gets the value of the 'end' field */
    public java.lang.Object getEnd() {
      return end;
    }
    
    /** Sets the value of the 'end' field */
    public influent.idl.FL_BoundedRange.Builder setEnd(java.lang.Object value) {
      validate(fields()[1], value);
      this.end = value;
      fieldSetFlags()[1] = true;
      return this; 
    }
    
    /** Checks whether the 'end' field has been set */
    public boolean hasEnd() {
      return fieldSetFlags()[1];
    }
    
    /** Clears the value of the 'end' field */
    public influent.idl.FL_BoundedRange.Builder clearEnd() {
      end = null;
      fieldSetFlags()[1] = false;
      return this;
    }

    /** Gets the value of the 'inclusive' field */
    public java.lang.Boolean getInclusive() {
      return inclusive;
    }
    
    /** Sets the value of the 'inclusive' field */
    public influent.idl.FL_BoundedRange.Builder setInclusive(boolean value) {
      validate(fields()[2], value);
      this.inclusive = value;
      fieldSetFlags()[2] = true;
      return this; 
    }
    
    /** Checks whether the 'inclusive' field has been set */
    public boolean hasInclusive() {
      return fieldSetFlags()[2];
    }
    
    /** Clears the value of the 'inclusive' field */
    public influent.idl.FL_BoundedRange.Builder clearInclusive() {
      fieldSetFlags()[2] = false;
      return this;
    }

    /** Gets the value of the 'type' field */
    public influent.idl.FL_PropertyType getType() {
      return type;
    }
    
    /** Sets the value of the 'type' field */
    public influent.idl.FL_BoundedRange.Builder setType(influent.idl.FL_PropertyType value) {
      validate(fields()[3], value);
      this.type = value;
      fieldSetFlags()[3] = true;
      return this; 
    }
    
    /** Checks whether the 'type' field has been set */
    public boolean hasType() {
      return fieldSetFlags()[3];
    }
    
    /** Clears the value of the 'type' field */
    public influent.idl.FL_BoundedRange.Builder clearType() {
      type = null;
      fieldSetFlags()[3] = false;
      return this;
    }

    @Override
    public FL_BoundedRange build() {
      try {
        FL_BoundedRange record = new FL_BoundedRange();
        record.start = fieldSetFlags()[0] ? this.start : (java.lang.Object) defaultValue(fields()[0]);
        record.end = fieldSetFlags()[1] ? this.end : (java.lang.Object) defaultValue(fields()[1]);
        record.inclusive = fieldSetFlags()[2] ? this.inclusive : (java.lang.Boolean) defaultValue(fields()[2]);
        record.type = fieldSetFlags()[3] ? this.type : (influent.idl.FL_PropertyType) defaultValue(fields()[3]);
        return record;
      } catch (Exception e) {
        throw new org.apache.avro.AvroRuntimeException(e);
      }
    }
  }
}
