// Copyright 2013 MIT Lincoln Laboratory, Massachusetts Institute of Technology 
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package mitll.xdata.ingest;

import mitll.xdata.db.DBConnection;
import mitll.xdata.db.H2Connection;
import mitll.xdata.db.MysqlConnection;
import org.apache.log4j.Logger;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.*;

public class BitcoinIngest {
  public static final boolean USE_TIMESTAMP = false;
  private static Logger logger = Logger.getLogger(BitcoinIngest.class);

  public static Map<String, String> TYPE_TO_DB = new HashMap<String, String>();
    static {
        TYPE_TO_DB.put("INTEGER", "INT");
        TYPE_TO_DB.put("STRING", "VARCHAR");
        TYPE_TO_DB.put("DATE", "TIMESTAMP");
        TYPE_TO_DB.put("REAL", "DOUBLE");
        TYPE_TO_DB.put("BOOLEAN", "BOOLEAN");
    }

  public static String createCreateSQL(String tableName, List<String> names, List<String> types, boolean mapTypes) {
        String sql = "CREATE TABLE " + tableName + " (" + "\n";
        for (int i = 0; i < names.size(); i++) {
          String statedType = types.get(i).toUpperCase();
          if (mapTypes) statedType = TYPE_TO_DB.get(statedType);
          if (statedType == null) logger.error("huh? unknown type " +types.get(i));
          sql += (i > 0 ? ",\n  " : "  ") + names.get(i) + " " + statedType;
        }
        sql += "\n);";
        return sql;
    }

    public static String createInsertSQL(String tableName, List<String> names) {
        String sql = "INSERT INTO " + tableName + " (";
        for (int i = 0; i < names.size(); i++) {
            sql += (i > 0 ? ", " : "") + names.get(i);
        }
        sql += ") VALUES (";
        for (int i = 0; i < names.size(); i++) {
            sql += (i > 0 ? ", " : "") + "?";
        }
        sql += ");";
        return sql;
    }

  /**
   * Adds equivalent dollar value column
   * @see #main
   * @param tableName bitcoin
   * @param dataFilename e.g. bitcoin-20130410.tsv
   * @param dbType h2 or mysql
   * @param useTimestamp true if we want to store a sql timestamp for time, false if just a long for unix millis
   * @throws Exception
   */
    public static void loadTransactionTable(String tableName, String dataFilename, String btcToDollarFile,
                                            String dbType, boolean useTimestamp) throws Exception {
      if (dbType.equals("h2")) tableName = tableName.toUpperCase();
      List<String> cnames = Arrays.asList("TRANSID", "SOURCE", "TARGET", "TIME", "AMOUNT", "USD", "DEVPOP", "CREDITDEV", "DEBITDEV");
  //    List<String> names = Arrays.asList("TRANSID", "SOURCE", "TARGET", "TIME", "AMOUNT", "USD");
      List<String> types = Arrays.asList("INT", "INT", "INT", useTimestamp ? "TIMESTAMP" : "LONG", "DECIMAL(20, 8)",
          "DECIMAL(20, 8)","DECIMAL","DECIMAL","DECIMAL"); // bitcoin seems to allow 8 digits after the decimal

      DBConnection connection = dbType.equalsIgnoreCase("h2") ?
          new H2Connection("bitcoin",10000000,true) : dbType.equalsIgnoreCase("mysql") ?
          new MysqlConnection("bitcoin") : null;

      if (connection == null) {
        logger.error("can't handle dbtype " + dbType);
        return;
      }

      String createSQL = createCreateSQL(tableName, cnames, types, false);

      long t = System.currentTimeMillis();
      logger.debug("dropping current " + tableName);
      doSQL(connection, "DROP TABLE " + tableName + " IF EXISTS");
      logger.debug("took " + (System.currentTimeMillis() - t) + " millis to drop " + tableName);
      doSQL(connection, createSQL);
      //doSQL(connection, "ALTER TABLE " + tableName + " ALTER COLUMN UID INT NOT NULL");
      //doSQL(connection, "ALTER TABLE " + tableName + " ADD PRIMARY KEY (UID)");

      RateConverter rc = new RateConverter(btcToDollarFile);

      BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(dataFilename), "UTF-8"));
      String line;
      int count = 0;
      long t0 = System.currentTimeMillis();
      int max = Integer.MAX_VALUE;
      int bad = 0;
    //  int black = 0;
      double totalUSD = 0;
      Map<Integer,UserStats> userToStats = new HashMap<Integer, UserStats>();

     // Set<Integer> userBlacklist = new HashSet<Integer>(Arrays.asList(25)); // skip supernode 25

      while ((line = br.readLine()) != null) {
        count++;
        if (count > max) break;
        String[] split = line.split("\\s+"); // 4534248 25      25      2013-01-27 22:41:38     9.91897304
        if (split.length != 6) {
          bad++;
          if (bad <10) logger.warn("badly formed line " + line);
        }

   //     int transid = Integer.parseInt(split[0]);
        int sourceid = Integer.parseInt(split[1]);
        int targetID = Integer.parseInt(split[2]);

        int i = 1;
    //    statement.setInt(i++, transid);
     //   statement.setInt(i++, sourceid);
      //  statement.setInt(i++, targetID);
        String day = split[3];
        Timestamp x = Timestamp.valueOf(day + " " + split[4]);
        if (useTimestamp) {
        //  statement.setTimestamp(i++, x);
        }
        else {
          //statement.setLong(i++,x.getTime());
        }

        double btc = Double.parseDouble(split[5]);
        //statement.setDouble(i++, btc);

        // do dollars
        Double rate = rc.getConversionRate(day, x.getTime());
        double usd = btc * rate;
        //statement.setDouble(i++, usd);
        totalUSD += usd;

        UserStats userStats = userToStats.get(sourceid);
        if (userStats == null) userToStats.put(sourceid, userStats = new UserStats());
        userStats.addDebit(usd);

        UserStats userStats2 = userToStats.get(targetID);
        if (userStats2 == null) userToStats.put(targetID, userStats2 = new UserStats());
        userStats2.addCredit(usd);

        if (count % 1000000 == 0) {
          logger.debug("count = " + count + "; " + (System.currentTimeMillis() - 1.0 * t0) / count
              + " ms/read");
        }
      }
      if (bad > 0) logger.warn("Got " + bad + " transactions...");
      br.close();


      double avgUSD = totalUSD/(double)count;
      List<double[]> feats = addFeatures(dataFilename, userToStats, avgUSD, rc);

       br = new BufferedReader(new InputStreamReader(new FileInputStream(dataFilename), "UTF-8"));
       count = 0;

      PreparedStatement statement;

      String insertSQL = createInsertSQL(tableName, cnames);
      statement = connection.getConnection().prepareStatement(insertSQL);

      while ((line = br.readLine()) != null) {
        double[] additionalFeatures = feats.get(count);
        count++;
        String[] split = line.split("\\s+"); // 4534248 25      25      2013-01-27 22:41:38     9.91897304

        int transid = Integer.parseInt(split[0]);
        int sourceid = Integer.parseInt(split[1]);
        int targetID = Integer.parseInt(split[2]);

        int i = 1;
        statement.setInt(i++, transid);
        statement.setInt(i++, sourceid);
        statement.setInt(i++, targetID);
        String day = split[3];
        Timestamp x = Timestamp.valueOf(day + " " + split[4]);
        if (useTimestamp) {
          statement.setTimestamp(i++, x);
        }
        else {
          statement.setLong(i++,x.getTime());
        }

        double btc = Double.parseDouble(split[5]);
        statement.setDouble(i++, btc);

        // do dollars
        Double rate = rc.getConversionRate(day, x.getTime());
        double usd = btc * rate;
        statement.setDouble(i++, usd);
        for (double feat : additionalFeatures) statement.setDouble(i++,feat);
        try {
          statement.executeUpdate();
        } catch (SQLException e) {
          logger.error("got error " + e + " on  " + line);
        }

        if (count % 1000000 == 0) {
          logger.debug("feats count = " + count + "; " + (System.currentTimeMillis() - 1.0 * t0) / count
              + " ms/insert");
        }
      }
      if (bad > 0) logger.warn("Got " + bad + " transactions...");
      br.close();
      statement.close();

      createIndices(tableName, connection);
      
      long t1 = System.currentTimeMillis();
        System.out.println("total count = " + count);
        System.out.println("total time = " + ((t1 - t0) / 1000.0) + " s");
        System.out.println((t1 - 1.0 * t0) / count + " ms/insert");
        System.out.println((1000.0 * count / (t1 - 1.0 * t0)) + " inserts/s");
    }

  private static void createIndices(String tableName, DBConnection connection) throws SQLException {
    long then = System.currentTimeMillis();
    doSQL(connection, "CREATE INDEX ON " + tableName + " (" + "SOURCE"+ ")");
    logger.debug("first index complete in " + (System.currentTimeMillis()-then));
    then = System.currentTimeMillis();
    doSQL(connection, "CREATE INDEX ON " + tableName + " (" + "TARGET" + ")");
    logger.debug("second index complete in " + (System.currentTimeMillis()-then));

    then = System.currentTimeMillis();
    doSQL(connection, "CREATE INDEX ON " + tableName + " (" + "TIME"+ ")");
    logger.debug("third index complete in " + (System.currentTimeMillis()-then));

    doSQL(connection, "create index " +
        //"idx_transactions_source_target" +
        " on " +
        tableName +
        "(" +
        "SOURCE"+", TARGET" +")");
    logger.debug("fourth index complete in " + (System.currentTimeMillis() - then));
  }

  private static List<double[]> addFeatures(
                           String dataFilename, Map<Integer, UserStats> userToStats,
                           double avgUSD,
                           RateConverter rc
  ) throws Exception {
    BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(dataFilename), "UTF-8"));
    String line;
    int count = 0;
    long t0 = System.currentTimeMillis();
    int max = Integer.MAX_VALUE;
    int bad = 0;
   // List<String> cnames = Arrays.asList("DEVPOP", "CREDITDEV", "DEBITDEV");
    List<double[]> feats = new ArrayList<double[]>();

    while ((line = br.readLine()) != null) {
      count++;
      if (count > max) break;
      String[] split = line.split("\\s+"); // 4534248 25      25      2013-01-27 22:41:38     9.91897304
      if (split.length != 6) {
        bad++;
        if (bad <10) logger.warn("badly formed line " + line);
      }

      try {
        int sourceid = Integer.parseInt(split[1]);
        int targetID = Integer.parseInt(split[2]);

        String day = split[3];
        Timestamp x = Timestamp.valueOf(day + " " + split[4]);

        double btc = Double.parseDouble(split[5]);

        // do dollars
        Double rate = rc.getConversionRate(day, x.getTime());
        double usd = btc * rate;

        double devFraction = (usd-avgUSD)/avgUSD;
        //    statement.setDouble(i++, devFraction);
        double[] addFeats = new double[3];
        addFeats[0] = devFraction;
        UserStats sourceStats = userToStats.get(sourceid);

        double avgCredit = sourceStats.getAvgCredit();
        double cdevFraction = avgCredit == 0 ? -1 : (usd - avgCredit)/avgCredit;
        addFeats[1] = cdevFraction;

        UserStats targetStats = userToStats.get(targetID);

        double avgDebit = targetStats.getAvgDebit();
        double ddevFraction = avgDebit == 0 ? -1 : (usd - avgDebit)/avgDebit;
        addFeats[2] = ddevFraction;
        feats.add(addFeats);

        if (count < 100) {
          logger.debug("source " + sourceid + " target " +targetID+" $"+ usd + " avg " + avgUSD +
              " dev " + devFraction +
              " cavg  " + avgCredit +
              " cdev " + cdevFraction +
              " davg  " + avgDebit +
              " ddev " + ddevFraction);
        }


        if (count % 1000000 == 0) {
          logger.debug("count = " + count + "; " + (System.currentTimeMillis() - 1.0 * t0) / count
              + " ms/insert");
        }
      } catch (Exception e) {
        logger.error("got " + e + " on " + line, e);
      }
    }
    if (bad > 0) logger.warn("Got " + bad + " transactions...");
    br.close();
    //statement.close();
     return feats;
  }

  public static class RateConverter {
    SortedMap<Long, Double> btcToDollar;
    long firstDate;
    // long earliest;
    double first;
    long lastDate;
    // long latest;
    double last;

    public RateConverter(String btcToDollarFile) throws Exception {
      btcToDollar = getBTCToDollar(btcToDollarFile);
      firstDate = btcToDollar.firstKey();
      // earliest = Timestamp.valueOf(firstDate + " 00:00:00").getTime();
      first = btcToDollar.get(firstDate);
      lastDate = btcToDollar.lastKey();
      // latest = Timestamp.valueOf(lastDate + " 00:00:00").getTime();
      last = btcToDollar.get(lastDate);
    }

    SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd");
    Map<String, Long> dayToTime = new HashMap<String, Long>();

    public Double getConversionRate(
        String day, long time) throws Exception {
      if (dayToTime.containsKey(day)) return getConversionRate(dayToTime.get(day), time);
      else {
        Date parse = sdf.parse(day);
        dayToTime.put(day, parse.getTime());
        return getConversionRate(parse.getTime(), time);
      }

    }

    public Double getConversionRate(
        long day, long time) {
      Double rate = btcToDollar.get(day);
      if (rate == null) {
        if (time < firstDate) rate = first;
        else if (time > lastDate) rate = last;
      }
      if (rate == null) {
        logger.warn("can't find btc->dollar rate for " + day);
        rate = 0d;
      }
      return rate;
    }

    public SortedMap<Long, Double> getBTCToDollar(String btcToDollarFile) throws Exception {
      BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(btcToDollarFile), "UTF-8"));
      String line;
      int count = 0;
      long t0 = System.currentTimeMillis();
      int max = Integer.MAX_VALUE;
      int bad = 0;
      SimpleDateFormat sdf = new SimpleDateFormat("MM/dd/yyyy");
      SortedMap<Long, Double> timeToRate = new TreeMap<Long, Double>();
      while ((line = br.readLine()) != null) {
        count++;
        if (count > max) break;
        String[] split = line.split("\\s+"); //  2013-01-27   9.91897304
        if (split.length != 2) {
          bad++;
          if (bad < 10) logger.warn("badly formed line " + line);
        }
        String s = split[0];
        Date parse = sdf.parse(s);
        timeToRate.put(parse.getTime(), Double.parseDouble(split[1]));
      }

      if (bad > 0) logger.warn("Got " + bad + " transactions...");
      br.close();
      return timeToRate;
    }
  }
  /*
  public static Map<String,Integer> getKeyToUser(String tableName, String dataFilename) throws Exception {
                                                            Map<String,Integer> keyToUser = new HashMap<String, Integer>();

    BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(dataFilename), "UTF-8"));
    String line;
    int count = 0;
    long t0 = System.currentTimeMillis();
    int max = 10;
    int bad = 0;
    while ((line = br.readLine()) != null) {
      count++;
      //if (count > max) break;
      String[] split = line.split("\\s+"); // 4534248 25      25      2013-01-27 22:41:38     9.91897304
      String user = split[0];
      String keys = split[1];
      for (String key : keys.split(",")) {
        //int ikey = Integer.parseInt(key);
        if (keyToUser.containsKey(ikey)) {
          logger.error("huh? existing user " + keyToUser.get(ikey) + " for  "  +ikey);
        }
        else {
          keyToUser.put(ikey,Integer.parseInt(user));
        }
      }
      if (split.length != 6) {
        bad++;
        if (bad <10) logger.warn("badly formed line " + line);
      }
      //List<String> values = Arrays.asList(split[0], split[1], split[2], split[3] + " " + split[4], split[5]);
      //List<String> values = split(line, "\t");
      int i = 1;
      statement.setInt(i++, Integer.parseInt(split[0]));
      statement.setInt(i++, Integer.parseInt(split[1]));
      statement.setInt(i++, Integer.parseInt(split[2]));
      statement.setTimestamp(i++, Timestamp.valueOf(split[3] + " " + split[4]));
      statement.setDouble(i++, Double.parseDouble(split[5]));
      try {
        statement.executeUpdate();
      } catch (SQLException e) {
        logger.error("got error " + e + " on  " + line);
      }

      //executePreparedStatement(statement, types, values);
      if (count % 10000 == 0) {
        logger.debug("count = " + count + "; " + (System.currentTimeMillis() - 1.0 * t0) / count
            + " ms/insert");
      }
    }
    br.close();

    statement.close();

    long t1 = System.currentTimeMillis();
    System.out.println("total count = " + count);
    System.out.println("total time = " + ((t1 - t0) / 1000.0) + " s");
    System.out.println((t1 - 1.0 * t0) / count + " ms/insert");
    System.out.println((1000.0 * count / (t1 - 1.0 * t0)) + " inserts/s");
  }*/


  private static void doSQL(DBConnection connection, String createSQL) throws SQLException {
    Connection connection1 = connection.getConnection();
    PreparedStatement statement = connection1.prepareStatement(createSQL);
    statement.executeUpdate();
    statement.close();
  }

/*  public static void testTabs(String dataFilename) throws Exception {
        BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(dataFilename), "UTF-8"));
        String line = null;
        int count = 0;
        int firstNumTabs = -1;
        while ((line = br.readLine()) != null) {
            count++;
            int numTabs = 0;
            boolean lastTabLastCharacter = false;
            for (int i = 0; i < line.length(); i++) {
                if (line.charAt(i) == '\t') {
                    numTabs++;
                    if (i == line.length() - 1) {
                        lastTabLastCharacter = true;
                    }
                }
            }
            if (firstNumTabs == -1) {
                firstNumTabs = numTabs;
                System.out.println("firstNumTabs = " + firstNumTabs);
            }
            if (numTabs != firstNumTabs) {
                System.out.println("line " + count + ": numTabs = " + numTabs);
            }
            if (lastTabLastCharacter) {
                System.out.println("line " + count + ": lastTabLastCharacter = " + lastTabLastCharacter);
                break;
            }
            if (count % 50000 == 0) {
                System.out.println("count = " + count);
            }
        }
        br.close();
    }*/

    public static void main(String[] args) throws Exception {
     // String tableName = "loanJournalEntriesLinks";
        //String schemaFilename = "kiva_schemas/" + tableName + ".schema";
      logger.debug("loading transactions");
        String dataFilename = "";//"/Users/go22670/xdata/datasets/bitcoin/transactions/bitcoin-20130410.tsv";
      if (args.length > 0) {
        dataFilename = args[0];
        logger.debug("got " + dataFilename);
      }
      String btcToDollarFile = "src" +File.separator + "main" + File.separator + "resources" +
          File.separator +
          "bitcoin_feats_tsv" +
          File.separator +
          "btcToDollarConversion.txt";
      File file = new File(btcToDollarFile);
      if (! file.exists()) logger.warn("can't find " + file.getAbsolutePath());
      loadTransactionTable("transactions", dataFilename, btcToDollarFile,"h2", USE_TIMESTAMP);
      logger.debug("done loading transactions");

      System.out.println("done");
    }
}
