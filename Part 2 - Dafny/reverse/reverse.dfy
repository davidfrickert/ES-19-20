/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

method countItem(arr: array<byte>, item: byte) returns (count: nat) 
requires arr.Length > 0
// ensures count == countF(arr[..], item)
{
  var i := 0;
  count := 0;

  
  while (i < arr.Length) 
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

method splitArrayBy(arr: array<byte>, item: byte) returns (a: array<seq<byte>>)
requires arr.Length > 0
{
  var from := 0;
  var to := 0;
  var l_cnt := 0;
  var lines := countItem(arr, item);

  // se alguem souber como se faz um array sem ser com o new q substitua isto, é para caso não houver newline retorna tudo um array com a seq toda
  if lines == 0 {
    a := new seq<byte>[1];
    a[0] := arr[..];
    return a;
  }

  a := new seq<byte>[lines];

  while(to < arr.Length && from < arr.Length) 
  decreases arr.Length - to
  decreases arr.Length - from
  invariant l_cnt < lines
  invariant to + 1 > from
  {

    if (arr[to] == item) {
      a[l_cnt] := arr[from..to + 1];
      // if para não dar erro no a[l_cnt] + invariant
      if l_cnt < lines - 1 { l_cnt := l_cnt + 1; }
      
      from := to;
    } 

    to := to + 1;

  }
  
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
    var ncmd := HostConstants.NumCommandLineArgs(env);
    print ncmd; print "\n";

    if ncmd != 3 {
      print ncmd; print " files supplied.";
      print "Command requires src file and dst file... Example: ./reverse.exe Source Dest";
      return;
    }

    var srcFile := HostConstants.GetCommandLineArg(1, env);
    var dstFile := HostConstants.GetCommandLineArg(2, env);

    var ok;

    ok := FileStream.FileExists(srcFile, env);

    if !ok {
      print "Source file doesn't exist.. Exiting";
      return;
    }

    var len;

    ok, len := FileStream.FileLength(srcFile, env);

    if !ok {
      print "File length failed... Exiting";
      return;
    }

    var fs;

    ok, fs := FileStream.Open(srcFile, env);

    if !ok {
      print "Failed to open file "; print srcFile; print "\n";
      return;
    }

    var buffer := new byte[len];

    ok := fs.Read(0, buffer, 0, len);

    if !ok {
      print "Failed to read source file '"; print srcFile; print "'\n";
      return;
    }

    var i := buffer.Length;
    if i > 0 {
      print buffer[i - 1]; print "\n";
    }

    print buffer[..]; print "\n";

    ok := fs.Close();

    if buffer.Length == 0 {
      return;
    }
    var res := splitArrayBy(buffer, 10);

    if res.Length > 1 {
      print res[1];
    }

}
