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

predicate sorted(s: seq<nat>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}


method Grep(word: array<char>, query: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length > 0
requires query.Length > 0
requires word.Length >= query.Length
//ensures forall v :: 0 <= v < |indexes| ==> indexes[v] < word.Length
ensures forall k :: 0 <= k < |indexes| ==> indexes[k] < word.Length
ensures forall k :: 0 <= k < |indexes| ==> indexes[k] + query.Length <= word.Length
{
  var i, j, pos: nat := 0, 0, 0;
  indexes := [];

  while (i < word.Length) 
  invariant i <= word.Length
  invariant j < query.Length
  invariant j <= i
  invariant 0 <= pos <= i - j
  invariant forall k :: 0 <= k < |indexes| ==> indexes[k] < word.Length
  invariant forall k :: 0 <= k < |indexes| ==> indexes[k] <= word.Length - query.Length
  //invariant sorted(indexes)

  decreases word.Length - i
  // j > 0 && j < query.Length && i >= 0 && i < word.Length && w
  // decreases if inRange(i, word.Length, j, query.Length) && word[i] == query[j] then query.Length - j else if inRange(i, word.Length, j, query.Length) &&  word[i] != query[j] && j > 0 then i - word.Length else word.Length - i
  {
    var increment_j := false;
    if word[i] == query[j] {
      if j == 0 {
        found, pos := true, i;  
      }
      increment_j := true;
    } else if j > 0 {
      pos, j, found := 0, 0, false;
      
      if word[i] == query[j] {
        found, increment_j, pos := true, true, i;
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
    return true, indexes;
  }
 
}

method CastArray(a: array<byte>) returns (chars: array<char>)
requires a.Length > 0
ensures fresh(chars)
ensures a.Length == chars.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] as char == chars[i]

{
  chars := new char[a.Length] (i requires 0 <= i < a.Length reads a => a[i] as char);
}

method BashGrep(word: array<char>, query: array<char>) returns (found: bool, rst: seq<char>)
requires word.Length > 0
requires query.Length > 0
requires word.Length >= query.Length
{
  var indexes;
  found, indexes := Grep(word, query);

  if !found {
    rst := [];
    return found, rst;
  }

  var wordSeq := word[..];
  rst := [];
  var i := 0;
  while i < |indexes| 
  
  {
    var low, high := indexes[i], indexes[i] + query.Length;
    rst := rst + "<-" + wordSeq[low..high] + "->";

    low := high;
    if i < |indexes| - 1 {
      high := indexes[i + 1];
    } else {
      high := |wordSeq|;
    }
      // substituir isto pelo sorted
    if low < high {
      rst := rst + wordSeq[low..high];//"...";
    }
    
    i := i + 1;
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
    var word := CastArray(buffer);

    print "Word := ", word[..], "\n";
    print "Query := ", query[..], "\n";

    if word.Length < query.Length {
      print "File has fewer characters than query string, invalid use! Please add text to the file or query a smaller string.";
      return;
    }
  
    //var found, pos:= Grep(word, query);


    //if found {
    // print "YES",", ", pos;
    //}
    //else {
    //  print "NO";
    //}
    var found, rst := BashGrep(word, query);

    if found {
      print rst;
    }

}
