/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

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
      print buffer[i - 1] as char; print "\n";
    }

    ok := fs.Close();

}
