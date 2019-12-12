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

predicate IndexIsMatch(word: array<char>, query:array<char>, index: nat) 
reads word, query
requires index <= word.Length - query.Length
{
  forall k :: index <= k < index + query.Length ==> word[k] == query[k - index]
}
predicate IsMatchN(word: array<char>, query:array<char>, index: nat, n: nat) 
reads word, query
requires index <= word.Length - query.Length
requires n <= query.Length
{
  forall k :: index <= k < index + n ==> word[k] == query[k - index]
}

// se count words de index até index + query.Length
method IsMatch(word: array<char>, query: array<char>, index: int) returns (m: bool)
requires 0 <= index <= word.Length - query.Length
ensures m ==> IndexIsMatch(word, query, index)
{
  //var cnt := CountConsecutiveChars(word[index..index+query.Length], query[..]);
  var j := 0;
  while j < query.Length  && word[index + j] == query[j] 
  invariant index + j <= word.Length
  invariant j <= query.Length
  invariant IsMatchN(word, query, index, j)
  //invariant j + 1 == C(word[index..index + j + 1], query[..j + 1])
  {
    j := j + 1;
  }

  m := j == query.Length;
}

method  GrepNaive(word: array<char>, query: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length >= query.Length
requires word.Length > 0
requires query.Length > 0
ensures forall k :: 0 <= k < |indexes| ==> indexes[k] < word.Length
ensures forall k :: 0 <= k < |indexes| ==> indexes[k] + query.Length <= word.Length
ensures forall k :: 0 <= k < |indexes| ==> IndexIsMatch(word, query, indexes[k])

{
  var i := 0;
  found := false;
  indexes := [];


  while i <= word.Length - query.Length
  invariant forall k :: 0 <= k < |indexes| ==> indexes[k] < word.Length
  invariant forall k :: 0 <= k < |indexes| ==> indexes[k] + query.Length <= word.Length
  invariant forall k :: 0 <= k < |indexes| ==> IndexIsMatch(word, query, indexes[k])

  {
    //var j := CountWords(word[i..i+query.Length], query[..]);
    
    var m := IsMatch(word, query, i);

    if m {
      indexes := indexes + [i];
    }
    i := i + 1;
  }
  return |indexes| > 0, indexes;
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
  found, indexes := GrepNaive(word, query);

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
