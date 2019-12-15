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


predicate MatchesAtIndex(word: array<char>, query:array<char>, index: nat) 
reads word, query
requires index <= word.Length - query.Length
{
  forall k :: index <= k < index + query.Length ==> word[k] == query[k - index]
}


predicate MatchesUpToN(word: array<char>, query:array<char>, index: nat, n: nat) 
reads word, query

requires n <= query.Length
{
  if index > word.Length - query.Length then true
  else forall k :: index <= k < index + n ==> word[k] == query[k - index]
}



predicate ExistsOne<T(==)>(a: array<T>, item: T)
reads a
{
  exists i :: 0 <= i < a.Length && a[i] == item
}
predicate method IsSubsequence<T(==)>(q1: seq<T>, q2: seq<T>)
{
    exists offset: nat :: offset + |q2| <= |q1| && IsSubsequenceAtOffset(q1,q2,offset)
}

predicate method IsSubsequenceAtOffset<T(==)>(q1: seq<T>, q2: seq<T>, offset: nat)
{ 
    offset + |q2| <= |q1| && q2 <= q1[offset..]
}

predicate AnyMatch(word: array<char>, query: array<char>) 
reads word, query
{
  exists i :: 0 <= i <= word.Length - query.Length && MatchesAtIndex(word, query, i)
}
method KMPSearch(word: array<char>, pattern: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length > 0
requires pattern.Length > 0
requires word.Length >= pattern.Length
decreases *
ensures |indexes| >= 0
ensures forall k :: 0 <= k < |indexes| ==>indexes[k]+pattern.Length <= word.Length
//ensures forall k :: 0 <= k < |indexes| && |indexes| > 0 ==> word[indexes[k]..indexes[k]+pattern.Length] == pattern[0..pattern.Length]
{

  var j, k := 0, 0;
  found := false;

  //var table := KMPTable(pattern);
  
  /*if pattern.Length >= 8 {
    var t1 := Table(pattern, 0, 1);
    var t2 := Table(pattern, 1, 2);
    var t3 := Table(pattern, 2, 3);
    var t4 := Table(pattern, 3, 4);
    var t5 := Table(pattern, 4, 5);
    var t6 := Table(pattern, 5, 6);
    var t7 := Table(pattern, 6, 7);
    var t8 := Table(pattern, 7, 8);
    print t1, "/", t2, "/", t3, "/", t4, "/", t5, "/", t6, "/", t7, "/", t8;
  }*/
  //print "Table: "; print table[..]; print "\n";
  indexes := [];
  
  while j <= word.Length - pattern.Length
  //invariant ValueBelowIndex(table)
  //invariant forall i :: 0 <= i < table.Length ==> -1 <= table[i] < pattern.Length
  invariant 0 <= k < pattern.Length && k<=j
  invariant forall m :: 0 <= m < |indexes| ==> indexes[m] + pattern.Length <= word.Length
  invariant k == pattern.Length ==> word[indexes[|indexes|-1]..(j-k)+pattern.Length] == pattern[0..pattern.Length] && (j-k) in indexes
  invariant k == pattern.Length ==> MatchesAtIndex(word, pattern, j-k) && AnyMatch(word, pattern) && (j-k) in indexes
  //invariant forall i :: 0 <= i < |indexes| ==> MatchesAtIndex(word, pattern, indexes[i])
  invariant k <= pattern.Length
  invariant MatchesUpToN(word, pattern, j - k, k)
  decreases *
//  decreases word.Length - j, pattern.Length - table[k], pattern.Length - k
  {
    if word[j] == pattern[k]
    {
      print "Matched at j, k = ", j, ", ", k, "\n";
      
      assert MatchesUpToN(word, pattern, j - k, k);

      j := j + 1;
      k := k + 1;


      if k == pattern.Length {
        assert MatchesAtIndex(word, pattern, j - k);
        found := true;
        indexes := indexes + [j - k];
        //k := table[k];
        k := 0;
      }
    } else {
      var prev_k := k;
      k := 0;
      if prev_k == 0 {
        j := j + 1;
      }
      /*
      k := table[k];
      if k == -1 {
        j := j + 1;
        k := k + 1;
      }
      */
      
    }
  }
  //var n:=0;
 /*  while n < |indexes|
  {
    print word[indexes[n]..indexes[n]+pattern.Length];
    n := n + 1;
  } */

}
/*
lemma {:axiom} checkword(word:array<char>, pattern: array<char>, indexes: seq<nat> )
  requires word.Length > 0
  requires pattern.Length > 0
  requires word.Length >= pattern.Length
  requires forall m :: 0 <= m < |indexes| ==> indexes[m] + pattern.Length <= word.Length
  ensures forall m :: 0 <= m < |indexes| && |indexes| > 0 ==> pattern[0..pattern.Length] == word[indexes[m]..(indexes[m]+pattern.Length)]
*/

// Permite que o loop da criação da tabela termine
// Para qualquer indice da tabela o valor deve ser inferior ao seu indice
predicate ValueBelowIndex(a: array<int>)
reads a
{
  forall i :: 0 <= i < a.Length ==> a[i] < i
}



function method Table(ptn: array<char>, lower: int, upper:int): int
reads ptn
requires ptn.Length > 0
requires 0 <= lower < upper < ptn.Length
{
  if (upper - lower == 1 && ptn[upper] == ptn[0]) then -1
  else
    if IsSubsequence(ptn[..lower], ptn[lower..upper]) 
      then 
        if lower > 0 
          then 1 + Table(ptn, lower - 1, upper)
        else 1
    else 0
}


method  KMPTable(pattern: array<char>) returns (table: array<int>)
requires pattern.Length > 0
ensures table.Length == pattern.Length + 1
ensures fresh(table)
ensures ValueBelowIndex(table)
ensures table[table.Length - 1] >= 0 && table[0] == -1
ensures forall i :: 0 <= i < table.Length ==> -1 <= table[i] <= pattern.Length
{
  var pos, cnd := 1, 0;
  table := new int[pattern.Length + 1] (_ => 0);
  table[0] := -1;
  while pos < pattern.Length && cnd < pattern.Length - 1
  invariant forall i :: 0 <= i < table.Length ==> -1 <= table[i] <= pattern.Length
  invariant 0 <= cnd < table.Length - 1
  invariant pos >= cnd
  invariant ValueBelowIndex(table)
  decreases pattern.Length - pos
  invariant table[0] == -1
  { 
    if pattern[pos] == pattern[cnd] {
      table[pos] := table[cnd];
    } else {
      table[pos] := cnd;
      cnd := table[cnd];

      while cnd >= 0 && pattern[pos] != pattern[cnd] 
      invariant cnd >= -1
      decreases cnd
      {
        cnd := table[cnd];
      }
    }
    pos, cnd := pos + 1, cnd + 1;
  }
  
  table[table.Length - 1] := cnd;
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
   modifies env.ok
  modifies env.files
  decreases *
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
  
    var found, rst := KMPSearch(word, query);
  
    
    print rst;
    

}
