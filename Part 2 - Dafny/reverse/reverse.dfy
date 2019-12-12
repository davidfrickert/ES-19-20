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

method countItem(arr: array<byte>, item: byte) returns (count: nat) 
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

function countF(items: seq<byte>, item: byte): nat

{
  multiset(items)[item]
}

method splitArrayBy(arr: array<byte>, item: byte) returns (a: array<array<byte>>)
requires arr.Length > 0
ensures fresh(a) && a.Length > 0 && a.Length == countF(arr[0..arr.Length], item) + 1
{
  var from := 0;
  var to := 0;
  var l_cnt := 0;
  var lines := countItem(arr, item);
  lines := lines + 1;

  if lines == 0 {
    return new array<byte>[1] (_ => arr);
  }

  a := new array<byte>[lines];

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
      var n := [(10 as byte)];
      tmp := arr[from..] + n;
      a[l_cnt] := ArrayFromSeq(tmp);
      l_cnt := l_cnt + 1;
    } 
    to := to + 1;
  }
}

method Flatten(a: array<array<byte>>) returns (all_bytes: seq<byte>)
requires a.Length > 0
//requires forall i :: 0 <=i<a.Length ==> a[i].Length>0 && a.Length>0 
//ensures forall i, k:: 0 <=i<a.Length && 0 <= k < a[i].Length ==> a[i][k] in all_bytes[0..|all_bytes|]
ensures LengthSum(a[..a.Length]) == |all_bytes|
{
  var sum: int :=0;
  all_bytes := [];
  var line := 0;
  
  while ( line < a.Length) 
    decreases a.Length - line
    invariant 0 <= line <= a.Length
    invariant sum == LengthSum(a[..line])
    invariant |all_bytes| == sum
  {
    var inside := a[line];
    all_bytes := all_bytes + inside[..];
    lemmasum(a, sum);
    line := line + 1;
    sum := LengthSum(a[..line]);
  }
}

lemma lemmasum(a:array<array<byte>>, n:int)
  ensures forall i:: 0 <= i < a.Length && n == LengthSum(a[..i]) ==> (n + a[i].Length) == LengthSum(a[..i+1])


function method LengthSum(v:seq<array<byte>>): int
decreases v
{
  if |v| == 0 then 0
  else if |v| == 1 then v[0].Length
  else v[0].Length + LengthSum(v[1..])
}
   


predicate reversed (arr : array<array<byte>>, outarr: array<array<byte>>)
requires arr.Length > 0 && outarr.Length > 0
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}

method reverse(line: array<array<byte>>) returns (r: array<array<byte>>)
  modifies line;
  requires line.Length > 0;
 // requires forall i :: 0 <=i<line.Length ==> line[i].Length>0;
  ensures line.Length == r.Length && reversed(line, r);
{
  r := new array[line.Length];
  r := line;
  var i := 0;
  var l : int := line.Length - 1;
  //TODO fzr reverse em cada linha, fica melhor
   while i <= l
    invariant  0 <= i <= line.Length
    invariant r.Length == line.Length
    invariant forall k :: (0 <= k < i || l-i < k <= l) ==> (line[k] == r[l-k]) 
    decreases l-i
  {
    r[i] := line[line.Length-1-i];
    i := i + 1;
  } 
}


method {:main} Main(ghost env: HostEnvironment?)
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
    var dstFile := HostConstants.GetCommandLineArg(2, env);

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
      return;
    }
    
    var split := splitArrayBy(buffer, 10);
    
    var reverse := reverse(split);
  
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

    print "'"; print srcFile; print "' -> '"; print dstFile; print "'\n";

    

}
