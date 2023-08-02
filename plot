#!/usr/bin/perl

$type="linespoints";

while (@ARGV)
{
  $arg=shift;
  if ($arg eq "-o")
  {
    $outfile=shift;
      if ($outfile =~ /^"/)
    {
      while (!($outfile =~ /$"/))
      {
        $newword=shift;
        $outfile="$outfile $newword";
      }
    }
 print "Plot output to file $outfile\n";
  }
  elsif ($arg eq "-f") {$fast=1;}
  elsif ($arg eq "-p") {$type="points";}
  elsif ($arg eq "-np") {$type="lines";}
  elsif ($arg eq "-t")
  {
    $title=shift;
    if ($title =~ /^"/)
    {
      while (!($title =~ /$"/))
      {
        $newword=shift;
        $title="$title $newword";
      }
    }
  }
  elsif ($arg eq "-yl" || $arg eq "-ly")
  {
    $ylabel=shift;
     if ($ylabel =~ /^"/)
    {
      while (!($ylabel =~ /$"/))
      {
        $newword=shift;
        $ylabel="$ylabel $newword";
      }
    }
}
  elsif ($arg eq "-xl" || $arg eq "-lx")
  {
    $xlabel=shift;
     if ($xlabel =~ /^"/)
    {
      while (!($xlabel =~ /$"/))
      {
        $newword=shift;
        $xlabel="$xlabel $newword";
      }
    }
  }
  elsif ($arg eq "-l")
  {
    $logs=1;
  }
  elsif ($arg eq "-sly")
  {
    $semilogy=1;
  }
  elsif ($arg eq "-slx")
  {
    $semilogx=1;
  }
  else
  {
    $filelist[$nfiles]=$arg; 
    $nfiles++;
  }
}

$uid=int(rand(1e8));
$tempfile="plottemp$uid";

if ($nfiles == 0)
{
  open Data,">$tempfile";
  while (<STDIN>)
  {
    print Data $_;
  }
  $nfiles=1;
  $filelist[0]=$tempfile;
  close Data;
}

$scriptfile="plotscript$uid";
open Script,">$scriptfile";

if ($outfile)
{
  print Script "set terminal pdf size 8,6\nset output \"$outfile\"\n";
} 
elsif ($fast)
{
	  print Script "set terminal x11\n";
}

print Script "set title \"$title\"\n" if ($title);
print Script "set xlabel \"$xlabel\"\n" if ($xlabel);
print Script "set ylabel \"$ylabel\"\n" if ($ylabel);
print Script "set logscale\nset format y \"%.0e\"\nset format x \"%.0e\"\n" if ($logs==1);
print Script "set logscale y\n" if ($semilogy==1);
print Script "set logscale x\n" if ($semilogx==1);
print Script "plot ";
$i=1;
foreach $file (@filelist)
{
  # look at the first line and count columns to see if there are error bars
  open Test,"$file";

    $_=<Test>; 
    chomp; 
    @w=split; 
    $nen=@w;
  
  if ($nen > 2) {$mytype = "errorbars";} else {$mytype = $type;}


  if ($nfiles > 1) {print Script "\"$file\" with $mytype,";}
  else {print Script "\"$file\" with $mytype notitle";}

  $i++;
}

foreach $file (@filelist)
{
  `sort -g < $file > plottemplist`;
  `mv plottemplist $file`;
}

`gnuplot -persist $scriptfile 2>/dev/null`;

#print "-- gnuplot script file --\n";
#system("cat $scriptfile");
print "\n";

if (-e $tempfile) {`rm $tempfile`;}
if (-e $tempfile2) {`rm $tempfile2`;}
`rm $scriptfile`;
