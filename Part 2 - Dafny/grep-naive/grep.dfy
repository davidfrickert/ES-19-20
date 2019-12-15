/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"

// Auxiliary Methods / functions / predicates from reverse
method ArrayFromSeq<T>(s: seq<T>) returns (a: array<T>)
  ensures |s| == a.Length
  ensures a[0.. a.Length] == s
{
  a := new T[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method countItem<T(==)>(arr: array<T>, item: T) returns (count: nat) 
requires arr.Length > 0
ensures count == countF(arr[0..arr.Length], item)
{
  var i := 0;
  count := 0;

  while (i < arr.Length) 
  invariant i <= arr.Length && count == countF(arr[0..i], item) 
  decreases arr.Length - i
  {
    if arr[i] == item {
      count := count + 1;
    }
    i := i + 1;
  }
}

function countF<T>(items: seq<T>, item: T): nat

{
  multiset(items)[item]
}

method splitArrayBy<T(==)>(arr: array<T>, item: T) returns (a: array<array<T>>)
requires arr.Length > 0
ensures fresh(a) && a.Length > 0 && a.Length == countF(arr[0..arr.Length], item) + 1
{
  var from := 0;
  var to := 0;
  var l_cnt := 0;
  var lines := countItem(arr, item);
  lines := lines + 1;

  if lines == 0 {
    return new array<T>[1] (_ => arr);
  }

  a := new array<T>[lines];

  while(to < arr.Length && from < arr.Length && l_cnt < lines) 
  decreases arr.Length - to
  decreases arr.Length - from
  invariant l_cnt <= lines && to + 1 > from
  invariant to <= arr.Length && from <= arr.Length
  invariant a.Length == countF(arr[0..arr.Length], item) + 1
  {
    if (arr[to] == item){
      a[l_cnt] := ArrayFromSeq(arr[from..to + 1]);
      l_cnt := l_cnt + 1;
      from := to + 1;
    }
    if(l_cnt == lines-1 && to == arr.Length-1 ){
      var tmp := [];
      var n := [item];
      tmp := arr[from..] + n;
      a[l_cnt] := ArrayFromSeq(tmp);
      l_cnt := l_cnt + 1;
    } 
    to := to + 1;
  }
}

// End of Auxiliary from reverse


// Auxiliary methods / predicates / functions for grep

// True if at 'index' of word there is a match (all characters from query match all characters from 'index' to 'index' + query.Length)
// Equivalent to MatchesUpToN where n is the query length
predicate MatchesAtIndex(word: array<char>, query:array<char>, index: nat) 
reads word, query
requires index <= word.Length - query.Length
{
  MatchesUpToN(word, query, index, query.Length)
}

// True if at 'index', all characters match, up to 'n'
// If n == query.Length then it is a total match
// Else, it is a partial match
predicate MatchesUpToN(word: array<char>, query:array<char>, index: nat, n: nat) 
reads word, query
requires index <= word.Length - query.Length
requires n <= query.Length
{
  forall k :: index <= k < index + n ==> word[k] == query[k - index]
}

// True if there exists any word index that has a full match
predicate AnyMatch(word: array<char>, query: array<char>) 
reads word, query
{
  exists i :: 0 <= i <= word.Length - query.Length && MatchesAtIndex(word, query, i)
}

// Auxiliary method to transform array of bytes to array of char
method CastArray(a: array<byte>) returns (chars: array<char>)
requires a.Length > 0
ensures fresh(chars)
ensures a.Length == chars.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] as char == chars[i]

{
  chars := new char[a.Length] (i requires 0 <= i < a.Length reads a => a[i] as char);
}

// This method will check at index if there is a full match (i.e., all characters from query match in word)
// It will ensure that if m (match) then it is in fact a match (using predicate MatchesAtIndex)
// It also ensures that if m (match) then exists at least one index that is a match
method FullMatch(word: array<char>, query: array<char>, index: int) returns (m: bool)
requires 0 <= index <= word.Length - query.Length
ensures m <==> MatchesAtIndex(word, query, index)
ensures m ==> exists v :: 0 <= v <= word.Length - query.Length && MatchesAtIndex(word, query, v)
{
  var j := 0;
  while j < query.Length  && word[index + j] == query[j] 
  // Loop invariant says that there is a partial match from index to index + j
  // This is true because we only iterate if there is a match, and increment j
  // At exit of loop we ensure a full match because j == query.Length
  invariant j <= query.Length
  invariant MatchesUpToN(word, query, index, j)
  decreases query.Length - j
  {
    j := j + 1;
  }

  m := j == query.Length;
}

// Naive Grep method
// Returns boolean found if there is any match and also sequence of indexes where the match was found
// Ensures that all indexes are indeed a match and that if we found a match then we have atleast one match (pred AnyMatch)
method  GrepNaive(word: array<char>, query: array<char>) returns (found: bool, indexes: seq<nat>)
requires word.Length >= query.Length
requires word.Length > 0
requires query.Length > 0
ensures forall k :: 0 <= k < |indexes| ==> indexes[k] + query.Length <= word.Length && indexes[k] < word.Length && MatchesAtIndex(word, query, indexes[k])
ensures found ==> AnyMatch(word, query)
{
  var i, m := 0, false;
  found := false;
  indexes := [];


  while i <= word.Length - query.Length
  // Loop over word indexes, stopping before because last possible match is at word.Length - query.Length
  // As invariant we chose some sanity properties, such as any index should be between (inclusive) 0 and word.Length - query.Length
  // and should be less or equal than i
  // Then, we also needed to ensure that all indexes are indeed a match and that if we found any match then there exists atleast one index that is a match

  invariant forall k :: 0 <= k < |indexes| ==> 0 <= indexes[k] <= word.Length - query.Length
  invariant forall k :: 0 <= k < |indexes| ==> 0 <= indexes[k] <= i
  invariant forall k :: 0 <= k < |indexes| ==> MatchesAtIndex(word, query, indexes[k])
  invariant found ==> AnyMatch(word, query)
  decreases word.Length - query.Length - i
  {    
    m := FullMatch(word, query, i);

    if m {
      found := true;
      indexes := indexes + [i];
    }
    
    i := i + 1;
  }
}


// We also did the extra Bash Grep
// First, we split the word by newlines, and then we apply the GrepNaive method to each line, searching for the query
// To verify if this was done correctly, we ensured that the returned lines should be greater than the query
// And that every line returned should have atleast one match
method BashGrep(word: array<char>, query: array<char>) returns (found: bool, lines: seq<array<char>>)
requires word.Length > 0
requires query.Length > 0
requires word.Length >= query.Length
ensures forall k :: 0 <= k < |lines| ==> lines[k].Length >= query.Length
ensures forall k :: 0 <= k < |lines| ==> AnyMatch(lines[k], query)
{
  var indexes;
  var all := splitArrayBy(word, '\n');
  var line := 0;
  lines := [];

  while line < all.Length 
  invariant forall i :: 0 <= i < |lines| ==> lines[i].Length >= query.Length
  invariant forall i :: 0 <= i < |lines| ==> AnyMatch(lines[i], query)
  decreases all.Length - line
  {
    var cur := all[line];
    if cur.Length >= query.Length {
      found, indexes := GrepNaive(cur, query);
      if found {
        assert forall k :: 0 <= k < |indexes| ==> MatchesAtIndex(cur, query, indexes[k]);
        lines := lines + [cur];
      }
    }
    line := line + 1;
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
  
    var found, rst := BashGrep(word, query);

    if found {
      print "Matching lines\n";
      var l := 0;
      while l < |rst| 
      decreases|rst| - l
      {
        print rst[l][..]; 
        l := l + 1;
      }
    }

}
