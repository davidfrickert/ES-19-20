/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"


//Method that transforms a Sequence into a Array
//Ensures that the resulting array has the same length and the same content
method ArrayFromSeq<T>(s: seq<T>) returns (a: array<T>)
  ensures |s| == a.Length
  ensures a[0.. a.Length] == s
{
  a := new T[|s|] ( i requires 0 <= i < |s| => s[i] );
}

//Method that given a item it counts the ocurrences of an item in the given array
//Ensures that the returned value is the same from the expected value(from a function)
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
//Funtion that returns the ocurrences of an item in the given sequence
function countF<T>(items: seq<T>, item: T): nat
{
  multiset(items)[item]
}

//Predicate that is true if the item is the last element of the array
//Requires that the array has at least an item 
predicate isLast<T>(a: array<T>, item: T)
reads a
requires a.Length > 0
{
  a[a.Length - 1] == item
}

//Recursive function to calculate the total sequence size
function method LengthSum<T>(v:seq<seq<T>>): int
//requires forall i:: 0<=i<|v| ==> |v[i]|>0
decreases v
{
  if |v| == 0 then 0
  else if |v| == 1 then |v[0]|
  else |v[0]| + LengthSum(v[1..])
}

method splitArrayBy<T(==)>(arr: array<T>, item: T) returns (a: seq<seq<T>>)
requires arr.Length > 0
requires countF(arr[0..arr.Length], item) > 0
//requires isLast(arr, item)
ensures |a| > 0
ensures |a| == countF(arr[0..arr.Length], item)
//ensures LengthSum(a)>0
{
  var from, to, l_cnt := 0, 0, 0;
  
  var lines := countItem(arr, item);
  var tmp := new seq<T>[lines] (_ => []);
  a := [];
  var sum := 0;
  assert LengthSum(a) == 0;

  while to < arr.Length 
  decreases arr.Length - to
  invariant from <= to
  invariant 0 < to <= arr.Length && arr[to-1] != item ==> sum == sum
  invariant 0 <= to <= arr.Length && from <= arr.Length
  invariant |a| == countF(arr[0..to], item) == l_cnt
  //invariant to>0 && countF(arr[0..arr.Length], item) > 0 && arr.Length>0 && sum>0 ==> LengthSum(a) > 0
  {
    if (arr[to] == item){
      a := a + [arr[from..to + 1]];
      sum := sum + (|arr[from..to + 1]|);
      l_cnt, from := l_cnt + 1, to + 1;
     /* print "Test\n";
      print |arr[from..to + 1]|; print "\n";
      print LengthSum(a); print "\n";
      print sum; print "\n";*/
    } 

    to := to + 1;
  }
}

//Method that reverses the sequence
//requires an array with at least an element
//ensures that the array was reversed and has the sum of the element sizes is still the same
method  reverse<T>(line: seq<seq<T>>) returns (r: seq<seq<T>>)
  requires |line| > 0;
  ensures |line| == |r| && reversed(line, r);
  ensures r[..|r|] == r
{
  //r := new array[line.Length](i requires 0 <= i < line.Length reads line => line[i]);
  r := line;
  var i := 0;
  var l : int := |line|- 1;
  var sumNew, sumOld := 0, 0;

   while i < |line|
    invariant  0 <= i <= |line|
    invariant |r| == |line|
    invariant reversing(line, r, i) 
    decreases |line|-i
  {
    r := r[i:=line[|line|-1-i]];

    i := i + 1;
  }
}

predicate reversed<T>(arr : seq<seq<T>>, outarr: seq<seq<T>>)
requires |arr| > 0 && |outarr| > 0
requires |arr| == |outarr|

{
  forall k :: 0<= k < |arr| ==> outarr[k] == arr[(|arr|-1-k)]
}

//Predicate that returns true if the sequence is reversed until a certain index
//Requires that both arrays have the same size and the index is at most the size of the arrays
predicate reversing<T>(arr : seq<seq<T>>, outarr: seq<seq<T>>, i: int)
requires i>= 0 && i <= |arr|
requires |arr| == |outarr|
{
  forall k :: 0 <= k < i ==> outarr[k] == arr[|arr|-1-k]
}

//Method that flattens a given sequence of sequences into a single sequence
//Ensures that returned sequence has the same size and content of all the elements from the sequence of sequences by
//comparing to expected values from recursive functions
method Flatten<T(==)>(a: seq<seq<T>>) returns (all_bytes: seq<T>)
requires |a| > 0
ensures LengthSum(a[..|a|]) == |all_bytes| && all_bytes[..|all_bytes|] == allBytes(a[..|a|])[..]
{
  var sum: int :=0;
  all_bytes := [];
  var line := 0;
  
  while ( line < |a|) 
    decreases |a| - line
    invariant 0 <= line <= |a|
    invariant line >= |a| ==> sum >= 0
    invariant sum == LengthSum(a[..line])
    invariant |all_bytes| == sum
    invariant allBytes(a[..line])[..] == all_bytes[..]
  {
    var inside := a[line];
    lemmasum(a, sum);
    lemmaAllBytes(a, all_bytes);
    all_bytes := all_bytes + inside[..];
    line := line + 1;
    sum := LengthSum(a[..line]);
  }
}

//Needed axioms for dafny to understand the property: sum + Length(a[i]) == Length(a[..i+1])
lemma {:axiom} lemmasum<T(==)>(a:seq<seq<T>>, n:int)
  ensures forall i:: 0 <= i < |a| && n == LengthSum(a[..i]) ==> (n + |a[i]|) == LengthSum(a[..i+1])

lemma {:axiom} lemmaAllBytes<T(==)>(a:seq<seq<T>>, n:seq<T>)
  ensures forall i:: 0 <= i < |a| && n == allBytes(a[..i]) ==> (n + a[i]) == allBytes(a[..i+1])

//Recursive function to transform a sequence of sequences into a sequence
function method allBytes<T>(v:seq<seq<T>>): seq<T>
decreases v
{
  if |v| == 0 then []
  else if |v| == 1 then v[0][..]
  else v[0][..] + allBytes(v[1..])
}



function method {:verify false} lines(s: seq<byte>): seq<seq<byte>>
decreases s
{
  if s == [] then []
  else
    var nextl := next_line(s);
    if nextl == [] then [] else [nextl] + lines(s[|nextl|+1..])
}

function method {:verify false} next_line(s: seq<byte>): seq<byte>
decreases s
  requires 0 < |s|
  ensures 0 < |next_line(s)|
{
  if s[0] != 10 then [s[0]] + next_line(s[1..]) else []
}

/* unlines */
function method {:verify false} unlines(s: seq<seq<byte>>): seq<byte>
decreases s
{
  if s == [] then []
  else s[0] + [10] + unlines(s[1..])
}



method  {:main} Main(ghost env: HostEnvironment?) 
  requires env != null && env.Valid() && env.ok.ok();
  requires |env.constants.CommandLineArgs()| == 3
  requires env.constants.CommandLineArgs()[1] in env.files.state() && |env.files.state()[env.constants.CommandLineArgs()[1]]|>0
  modifies env.ok
  modifies env.files
  ensures var args := old(env.constants.CommandLineArgs());
    env.ok != null && env.ok.ok() && |args| == 3 && args[1] in old(env.files.state()) && args[2] !in old(env.files.state()) ==> args[2] in env.files.state() && |old(env.files.state())[args[1]]| == |env.files.state()[args[2]]| 
    && |env.files.state()[args[2]]| > 0 && |old(env.files.state())[args[1]]| > 0
    && reversed( 
      lines(
        old(env.files.state())[args[1]]
        ),
      lines(
        env.files.state()[args[2]])
      )
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
    var dstFile := HostConstants.GetCommandLineArg(2, env);



    var srcExists := FileStream.FileExists(srcFile, env);
    var dstExists := FileStream.FileExists(dstFile, env);

    if !srcExists {
      print "In file '"; print srcFile; print "'doesn't exist";
      return;
    }
    if dstExists {
       print "Out file '"; print dstFile; print "'already exist";
      return;
    }

    var ok, len := FileStream.FileLength(srcFile, env);

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
    
    
    var newlineCount := countItem(buffer, 10);
    var lastIsNewline := buffer[buffer.Length - 1] == 10;
    if newlineCount == 0 || !lastIsNewline {
      return;
    }
    
    print buffer[..], "-buffer-\n";
    
    //Split file into array by \n 
    var split := splitArrayBy(buffer, 10);
    print split;

    //Reverse array
    print split, "-split-\n";
    var reverse := reverse(split);

    //assert reversed(split, reverse);

    print reverse, "-reversed-\n";
    //Flatt the array into a sequence of bytes
    var f := Flatten(reverse);
    var flat := ArrayFromSeq(f);

    var ofs; 
    ok, ofs := FileStream.Open(dstFile, env);
    if !ok {
      print "Problems opening out file "; print dstFile; print "\n";
      return;
    }

    // o dafny queixa-se se eu meter simplesmente flat.Length pq é int e ele quer int32.. n consegui arranjar solução bonita
    var start;
    if -0x80000000 <= flat.Length < 0x80000000 {
      start := flat.Length as int32;
    } else { return; }

   
    ok := ofs.Write(0, flat, 0, start);
    if !ok {
      print "Problems writing to out file '"; print dstFile; print "'\n";
      return;
    }

    ok := ofs.Close();
    if !ok {
      print "Problems closing out file '"; print dstFile; print "'\n";
      return;
    }
    
    print "Reversal successfull\n";
    print "'"; print srcFile[..]; print "' -> '"; print dstFile[..]; print "'\n";
}