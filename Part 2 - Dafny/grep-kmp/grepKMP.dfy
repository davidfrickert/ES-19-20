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


method KMPnoTable(word: array<char>, pattern: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length > 0
requires pattern.Length > 0
requires word.Length >= pattern.Length
decreases *
ensures |indexes| >= 0
ensures forall k :: 0 <= k < |indexes| ==>indexes[k]+pattern.Length <= word.Length
ensures forall k :: 0 <= k < |indexes| && |indexes| > 0 ==> word[indexes[k]..indexes[k]+pattern.Length] == pattern[0..pattern.Length]
{
   var j, k := 0, 0;
  found := false;

  indexes := [];
  
  while j <= word.Length - pattern.Length
  invariant 0 <= k < pattern.Length && k<=j
  invariant forall m :: 0 <= m < |indexes| ==> indexes[m] + pattern.Length <= word.Length
  invariant k == pattern.Length ==> word[indexes[|indexes|-1]..(j-k)+pattern.Length] == pattern[0..pattern.Length] && (j-k) in indexes
  invariant k == pattern.Length ==> MatchesAtIndex(word, pattern, j-k) && AnyMatch(word, pattern) && (j-k) in indexes
  invariant forall i :: 0 <= i < |indexes| ==> MatchesAtIndex(word, pattern, indexes[i])
  invariant k <= pattern.Length
  invariant MatchesUpToN(word, pattern, j - k, k)
  decreases *
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
        k := 0;
      }
    } else {
      var prev_k := k;
      k := 0;
      if prev_k == 0 {
        j := j + 1;
      }
    }
  }

}

method  KMPEasy(word: array<char>, pattern: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length > 0
requires pattern.Length > 0
requires word.Length >= pattern.Length
decreases *
ensures |indexes| >= 0
ensures forall k :: 0 <= k < |indexes| ==>  indexes[k]+pattern.Length <= word.Length
ensures forall k :: 0 <= k < |indexes| && |indexes| > 0 ==> word[indexes[k]..indexes[k]+pattern.Length] == pattern[0..pattern.Length]
//ensures forall k :: 0 <= k < |indexes| ==> MatchesAtIndex(word, pattern, indexes[k])
{

  var j, k := 0, 0;
  var table := KMPTableEasy(pattern);
  print table[..], "\n";
  indexes := [];

  while j < word.Length 
  //Boundaries of the variables in the loop
  invariant forall i :: 0 <= i < table.Length ==> 0 <= table[i] < pattern.Length
  invariant 0 <= k < pattern.Length && k<=j && 0 <= j <= word.Length
  //An index of the start of the pattern + the pattern size cannot be bigger than the length of the sentence(word)
  invariant forall i :: 0 <= i < |indexes| ==> indexes[i] + pattern.Length <= word.Length
  //
  invariant k == pattern.Length ==> word[indexes[|indexes|-1]..(j-k)+pattern.Length] == pattern[0..pattern.Length] && (j-k) in indexes
  invariant k == pattern.Length ==> MatchesAtIndex(word, pattern, j-k) && AnyMatch(word, pattern) && (j-k) in indexes
  decreases *
//  decreases word.Length - j, pattern.Length - table[k], pattern.Length - k
  {
    if k < pattern.Length{
      if word[j] == pattern[k]
      {
        j := j + 1;
        k := k + 1;

        if k == pattern.Length {
         indexes := indexes + [j - k];
         k := table[k - 1];
       }
    } else {
        if k != 0 {
          k := table[k - 1];
        } else {
          j := j + 1;
        }
    }
    }
  }
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



function method VerifyTable(ptn: array<char>, lower: int, upper:int): int
reads ptn
decreases {ptn}, ptn, lower, upper
requires ptn.Length > 0
requires 0 <= lower < upper < ptn.Length
{
  if (upper - lower == 1 && ptn[upper] == ptn[0]) then -1
  else
    if IsSubsequence(ptn[..lower], ptn[lower..upper]) 
      then 
        if lower > 0 
          then 1 + VerifyTable(ptn, lower - 1, upper)
        else 1
    else 0
}

predicate  CheckTable(ptn: array<char>, index: nat, score: nat) 
requires score <= index < ptn.Length
reads ptn
{
  ptn[index + 1 - score..index + 1] == ptn[0..score]
}


//Method that does the pre processing, it fills the table with the values of the equal substring
//Requires that the pattern has at least a char
//Ensures that the values are in the respective boundaries
//And that given a value bigger than 0, the start of the pattern is equal to the previous substring at a certain point
//Notes: 1- defined boundaries like 1<i<=table.Length may seem that we ignore table[1], but in reality we use i-1, so we check from 1 to pattern-Length-1
//2-Trigger warning and post condition might not hold even though the invariants are accepted
method KMPTableEasy(pattern: array<char>) returns (table: array<int>) 
requires pattern.Length > 0
ensures pattern.Length == table.Length
ensures forall i:: 0 <= i < table.Length ==> 0 <= table[i] < pattern.Length
ensures forall i:: 0 <= i < table.Length ==> i-table[i] >= 0
ensures forall i:: 1 < i <= table.Length && table[i-1]>0 && (i-1)-(table[i-1]+1)>=0 ==> pattern[0..table[i-1]] == pattern[(i-1)-(table[i-1]+1)..i]
{

  table := new int[pattern.Length] (_ => 0);
  var i, j := 1, 0;


  //assume forall i:: 1 <= i < table.Length && table[i]>0 && i-1-table[i]>=0 ==> pattern[0..table[i]] == pattern[i-1-table[i]..i];
  
  while i < pattern.Length 
  decreases pattern.Length - i
  //Boundary invariants, initial value is always 0 and remaining values of table can be from 0 to pattern.Length-1  
  invariant j < i 
  invariant 1 <= i <= pattern.Length && table.Length == pattern.Length
  invariant 0 <= table[i-1] <= i    
  invariant table[0] == 0 && forall k:: 0 <= k < table.Length ==>  0 <= table[k] < pattern.Length
  //Difference between i and the value of the table must inside of the pattern length
  invariant forall i:: 0 <= i < table.Length ==> 0 <= i-table[i] < pattern.Length
  //Table properties
  //1-After entry, if the value table[i-1] is equal to j+1, it means that the char at pattern[i-1] is equal to the char at pattern[j]
  invariant   i>1 && table[i-1] == j+1 ==> pattern[i-1] == pattern[j]
  //2-If j its 0, it means that the char at pattern[i-1] is not equal to the char at pattern[j]
  invariant j==0 && pattern[j] != pattern[i-1]==> table[i-1] == 0
  //3- After entry if value of table is j+1(>=1), then the respective subsstring is equal to the respective start of the pattern
  invariant i>1 && table[i-1] == j-1 && (i-1)-(table[i-1]+1)>=0 ==> pattern[0..j-1] == pattern[(i-1)-(table[i-1]+1)..i]
  invariant i>1 && table[i-1] == 0 && (i-1)-(table[i-1]+1)>=0 ==> pattern[0..table[i-1]] != pattern[(i-1)-(table[i-1]+1)..i]

  {
    while j != 0 && pattern[j] != pattern[i]
     invariant 0 <= j
     invariant table[0] == 0
     decreases if j <= 0 then 0 - j else j - 0
    {
      j := table[j - 1];
    }

    if pattern[j] == pattern[i] {
      j := j + 1;
    }
    
    table[i] := j;
    i := i + 1;
   
  }
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
  
    var found, rst := KMPEasy(word, query);
  
    
    print rst;
    

}
