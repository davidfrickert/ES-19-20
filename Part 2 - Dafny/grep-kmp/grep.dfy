/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"


predicate inRange(i: int, len: int, j: int, len2: int) {
  0 <= i < len && 0 <= j < len2
}

method fillLps(query: array<char>) returns (lps: array<int>)
requires query.Length > 0
{
  lps := new int[query.Length];
  var len := 0;
  var i := 1;
  lps[0] := 0;

  while(i < query.Length)
  invariant i <= query.Length
  decreases query.Length - i
  {
    if(query[i] == query[len]){
      len := len + 1;
      lps[i] := len;
      i := i + 1;
    } else {
      if(len != 0){
        len := lps[len - 1];
      } 
        else {
          lps[i] := len;
          i := i + 1;
      }
    }

  }
}


method Grep(word: array<byte>, query: array<char>) returns (found: bool, pos: int)
requires word.Length > 0
requires query.Length > 0
{
  var lps := fillLps(query);
  var indexQuery, indexWord := 0, 0;
  while(indexWord< word.Length)
  decreases word.Length - indexWord
  {
    if(indexQuery < query.Length && indexWord < word.Length && query[indexQuery] == word[indexWord] as char){
      indexWord := indexWord+1;
      indexQuery := indexQuery+1;
    }
    if(indexQuery == query.Length){
      return true,indexWord-indexQuery;
    } else if(indexQuery < query.Length && indexWord < word.Length && query[indexQuery] != word[indexWord] as char){
      if(indexQuery != 0 && indexQuery < lps.Length){
        indexQuery := lps[indexQuery -1];  
      } else{
        indexWord := indexWord +1;
      }
    }
  }


}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
  var ncmd := HostConstants.NumCommandLineArgs(env);

    if ncmd != 3 {
      if ncmd >= 1 {
        print ncmd - 1; print " files supplied.\n";
      }
      print "Command requires stringQuery and file... Example: ./grep.exe Query File";
      return;
    }

    var query := HostConstants.GetCommandLineArg(1, env);
    var srcFile := HostConstants.GetCommandLineArg(2, env);
    var ok;

    ok := FileStream.FileExists(srcFile, env);

    if !ok {
      print "In file '"; print srcFile; print "'doesn't exist";
      return;
    }

    var len;

    ok, len := FileStream.FileLength(srcFile, env);

    if !ok {
      print "Couldn't stat file '"; print srcFile; print "' length";
      return;
    }
    
    var fs;

    ok, fs := FileStream.Open(srcFile, env);
    
    if !ok {
      print "Problems opening file "; print srcFile; print "\n";
      return;
    }

    var buffer := new byte[len];
    ok := fs.Read(0, buffer, 0, len);

    if !ok {
      print "Problems reading in file'"; print srcFile; print "'\n";
      return;
    }

    var i := buffer.Length;

    ok := fs.Close();

    if !ok {
      print "Problems closing in file '"; print srcFile; print "'\n";
      return;
    }

    if buffer.Length == 0 {
      print "File is empty, exiting.";
      return;
    }
    if query.Length == 0 {
      print "Empty query, exiting.";
      return;
    }

    var found, pos:= Grep(buffer, query);
    
    if found {
     print "YES",", ", pos;
    }
    else {
      print "NO";
    }
}
