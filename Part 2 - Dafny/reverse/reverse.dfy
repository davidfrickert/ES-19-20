/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

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

method Flatten<T(==)>(a: array<array<T>>) returns (all_bytes: seq<T>)
requires a.Length > 0
ensures LengthSum(a[..a.Length]) == |all_bytes| && all_bytes[..|all_bytes|] == allBytes(a[..a.Length])[..]
{
  var sum: int :=0;
  all_bytes := [];
  var line := 0;
  
  while ( line < a.Length) 
    decreases a.Length - line
    invariant 0 <= line <= a.Length
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

lemma {:axiom} lemmasum<T(==)>(a:array<array<T>>, n:int)
  ensures forall i:: 0 <= i < a.Length && n == LengthSum(a[..i]) ==> (n + a[i].Length) == LengthSum(a[..i+1])

lemma {:axiom} lemmaAllBytes<T(==)>(a:array<array<T>>, n:seq<T>)
  ensures forall i:: 0 <= i < a.Length && n[..] == allBytes(a[..i])[..] ==> (n + a[i][..]) == allBytes(a[..i+1])[..]



function method LengthSum<T>(v:seq<array<T>>): int
decreases v
{
  if |v| == 0 then 0
  else if |v| == 1 then v[0].Length
  else v[0].Length + LengthSum(v[1..])
}
   
function method allBytes<T>(v:seq<array<T>>): seq<T>
decreases v
reads v
{
  if |v| == 0 then []
  else if |v| == 1 then v[0][..]
  else v[0][..] + allBytes(v[1..])
}

predicate reversed<T>(arr : array<array<T>>, outarr: array<array<T>>)
requires arr.Length > 0 && outarr.Length > 0
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0<= k <arr.Length ==> outarr[k] == arr[(arr.Length-1-k)]
}

predicate reversing<T>(arr : array<array<T>>, outarr: array<array<T>>, i: int)
requires arr.Length > 0 && outarr.Length > 0
requires i>= 0 && i <= arr.Length
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length-1-k]
}

method reverse<T>(line: array<array<T>>) returns (r: array<array<T>>)
  requires line.Length > 0;
  ensures line.Length == r.Length && reversed(line, r);
{
  r := new array[line.Length](i requires 0 <= i < line.Length reads line => line[i]);
  var i := 0;
  var l : int := line.Length - 1;

   while i < line.Length
    invariant  0 <= i <= line.Length
    invariant r.Length == line.Length
    invariant reversing(line, r, i) 
    decreases line.Length-i
  {
    r[i] := line[line.Length-1-i];
    i := i + 1;
  } 
}


/* lines */
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




method {:main} Main(ghost env: HostEnvironment?) 
  requires env != null && env.Valid() && env.ok.ok();
  requires |env.constants.CommandLineArgs()| == 3
  requires env.constants.CommandLineArgs()[1] in env.files.state() && |env.files.state()[env.constants.CommandLineArgs()[1]]|>0
  modifies env.ok
  modifies env.files
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[1] in env.files.state()
  //ensures env.files.state()[env.constants.CommandLineArgs()[1]] == []\
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
       print "In file '"; print dstFile; print "'already exist";
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

    if buffer.Length == 0 {
      return;
    }
    
    //Split file into array by \n 
    var split := splitArrayBy(buffer, 10);
    //Reverse array
    var reverse := reverse(split);
    //Flatt the array into a sequence of bytes
    var f := Flatten(reverse);
    var flat := ArrayFromSeq(f);

    var t := 0;
    var ofs; ok, ofs := FileStream.Open(dstFile, env);
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

    /*
    var in_bytes := ArrayFromSeq(env.files.state()[srcFile[..]]);
    var out_bytes := ArrayFromSeq(env.files.state()[dstFile[..]]);
    var f_in := splitArrayBy(in_bytes, 10);
    var f_out := splitArrayBy(out_bytes, 10);


    assert dstFile[..] in env.files.state();
    assert reversed(f_in, f_out);
    */

    print "Reversal successfull\n";
    print "'"; print srcFile; print "' -> '"; print dstFile; print "'\n";
}
