/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"


method ArrayFromSeq<T>(s: seq<T>) returns (a: array<T>)
  ensures a[0.. a.Length] == s
{
  a := new T[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method CastArray(a: array<byte>) returns (chars: array<char>)
requires a.Length > 0
ensures fresh(chars)
ensures a.Length == chars.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] as char == chars[i]

{
  chars := new char[a.Length] (i requires 0 <= i < a.Length reads a => a[i] as char);
}

method GrepKMP(word: array<char>, pattern: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length > 0
requires pattern.Length > 0
{
  var M, N := pattern.Length, word.Length;
}

method {:verify false} KMPSearch(word: array<char>, pattern: array<char>) returns (indexes: seq<nat>)
requires word.Length > 0
requires pattern.Length > 0
requires word.Length >= pattern.Length
{
  var j, k := 0, 0;
  var table := KMPTable(pattern);
  while j < word.Length 
  {
    if word[j] == pattern[k]
    {
      j := j + 1;
      k := k + 1;
      if k == pattern.Length {
        indexes := indexes + [j - k];
        k := table[k];
      }
    } else {
      k := table[k];
      if k < 0 {
        j := j + 1;
        k := k + 1;
      }
    }
  }
}
method {:verify false} KMPTable(pattern: array<char>) returns (table: array<int>)
requires pattern.Length > 0
ensures table.Length == pattern.Length + 1
{
  var pos, cnd := 1, 0;
  table := new int[pattern.Length + 1];
  table[0] := -1;
  
  while pos < pattern.Length
  {
    if pattern[pos] == pattern[cnd] {
      table[pos] := table[cnd];
    } else {
      table[pos] := cnd;
      cnd := table[cnd];
      while cnd >= 0 && pattern[pos] != pattern[cnd] 
      {
        cnd := table[cnd];
      }
    }
    pos, cnd := pos + 1, cnd + 1;
  }
  table[pos] := cnd;

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
  
    var rst := KMPSearch(word, query);

    
    print rst;
    

}
