/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

method ArrayFromSeq<T>(s: seq<T>) returns (a: array<T>)
  ensures a[..] == s
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
  // invariante para provar a pós-condição comentada?
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
ensures fresh(a)
ensures a.Length > 0
{
  var from := 0;
  var to := 0;
  var l_cnt := 0;
  var lines := countItem(arr, item);

  if lines == 0 {
    return new array<byte>[1] (_ => arr);
  }

  a := new array<byte>[lines];

  while(to < arr.Length && from < arr.Length && l_cnt < lines) 
  decreases arr.Length - to
  decreases arr.Length - from
  invariant l_cnt <= lines
  invariant to + 1 > from
  {

    if (arr[to] == item) {
      a[l_cnt] := ArrayFromSeq(arr[from..to + 1]);
      l_cnt := l_cnt + 1;
      from := to + 1;
    } 

    to := to + 1;

  }
  
}

method Flatten(a: array<array<byte>>) returns (f: array<byte>) 

{
  var all_bytes := [];
  var line := 0;

  while ( line < a.Length) 

  {
    all_bytes := all_bytes + a[line][..];
    line := line + 1;
  }

  f := ArrayFromSeq(all_bytes);

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
    var res := splitArrayBy(buffer, 10);
    var flat := Flatten(res);
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
