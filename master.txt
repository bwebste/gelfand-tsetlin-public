############################################
# Loads original functions and red functions
#
# Runs a couple test cases at start up
############################################

#in order to do computations, run "gap.sh master.gap" (with appropriate paths thrown in).
#This will put you in a GAP environment with all commands loaded.  

directory:=Directory(".");
Read(Filename(directory,"klr-red.gap"));
Read(Filename(directory,"compute-red.gap"));

#Some lines you can uncomment if you want to do specific computations:
#for the integral case of sl3
#ComputeRed([1,2,3]);
#for the integral case of sl4
#ComputeRed([1,2,3,4]);
#if you're brave enough, integral case of sl5
#ComputeRed([1,2,3,4,5]);
#uncomment this is you want to print your computation at the end.
#PrintIC(IC);

#To output a table like in the paper use
#MakeTable([1,2,3]);
#or to only get a range of columns, use
#MakeTableP([1,2,3,4],1,20,0);
#This only gives the first 20 columns (and will only compute the characters for those simples, so it is faster than doing all of them).
#If you increase the last input to n, then you'll only get simples that have a multiplicity that large.  

#To compute the number of integral simples in the regular block for gl(3), gl(4), etc.
#CheckNumber(3);
#CheckNumber(4);

