/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"

predicate inRange(i: int, len: int, j: int, len2: int) {
  0 <= i < len && 0 <= j < len2
}

method Grep(word: array<byte>, query: array<char>) returns (found: bool, indexes: seq<int>)
requires word.Length > 0
requires query.Length > 0
{
  var i, j, pos := 0, 0, 0;
  indexes := [];

  while (i < word.Length) 
  invariant i <= word.Length
  invariant j < query.Length
  invariant j <= i
  // j > 0 && j < query.Length && i >= 0 && i < word.Length && w
  // decreases if inRange(i, word.Length, j, query.Length) && word[i] == query[j] then query.Length - j else if inRange(i, word.Length, j, query.Length) &&  word[i] != query[j] && j > 0 then i - word.Length else word.Length - i
  {
    var increment_j := false;
    if word[i] as char == query[j] {
      if j == 0 {
        found := true;  
        pos := i;    
      }
      increment_j := true;
    } else if j > 0 {
      var p_j := j;
      j, found, pos := 0, false, -1;
    
      if p_j > 0 && word[i] as char == query[j] {
        found := true;
        pos := i;
        increment_j := true;
      }
      //i := i - 1;
    } 
    if j == query.Length - 1 {
      if found {
        indexes := indexes + [pos];
        pos, j, found := 0, 0, false;
      }
    } else if increment_j{
      j := j + 1;
    }
    i := i + 1;
  }
  
  if !found && |indexes| > 0 {
    found := true;
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
      print "Command requires src file and dst file... Example: ./reverse.exe Source Dest\n";
      return;
    }

    var srcFile := HostConstants.GetCommandLineArg(1, env);
    var query := HostConstants.GetCommandLineArg(2, env);

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
