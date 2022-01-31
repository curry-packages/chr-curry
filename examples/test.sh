#!/bin/sh
# Shell script to test the current set of CHR(Curry) examples

VERBOSE=no # no longer used...
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

# Extract information about the back end:
BACKEND=`$CURRYBIN --noreadline :set v0 :set -time :load Curry.Compiler.Distribution :eval "putStrLn (curryRuntime ++ show curryRuntimeMajorVersion)" :quit 2> /dev/null`
# check back end:
if [ "$BACKEND" != sicstus4 -a "$BACKEND" != swi6 -a "$BACKEND" != swi7 -a "$BACKEND" != swi8 ] ; then
  echo "No appropriate Prolog back end, skip the CHR tests."
  exit
fi

LOGFILE=xxx$$
/bin/rm -rf .curry
cat << EOM | $CURRYBIN -q :set -interactive :set v0 :set printdepth 0 :set -time :set +echo | tee $LOGFILE
:load Leq
main10 x        where x free
main11 (x::Int) y z    where x,y,z free
main12 (x::Int) y z z' where x,y,z,z' free

:load Bool
main20 x y z    where x,y,z free
main21 a b s c  where a,b,s,c free
main22 a b s c  where a,b,s,c free

:load GCD
main30
main31
compileGCD
:load GCDCHR
solveCHR $ gcdanswer x /\ gcd 206 /\ gcd 40  where x free

:load Fib
main41 x    where x free
compileFib
:load FIBCHR
solveCHR $ fib 20 x  where x free

:load FD
main50 x y      where x,y free
main51 x        where x free
main52 [x,y,z]  where x,y,z free
main53 xs       where xs free
main55 xs       where xs free

:load UnionFind
main60
main61 x        where x free
main62 x y      where x,y free
main63
main64 x y      where x,y free
main65 x y      where x,y free
compileUF
:load UFCHR
solveCHR $ andCHR [make (1::Int), make 2, make 3, make 4, make 5, union 1 2, union 3 4, union 5 3, find 2 x, find 4 y]  where x,y free

:load Primes
main70

:load Gauss
main80 x y      where x,y free
main81 x y      where x,y free
main82 x y      where x,y free
main85 i        where i free
main86 i        where i free

EOM
# clean up:
for p in GCDCHR FIBCHR UFCHR GAUSSCHR ; do
    /bin/rm -f $p*
done
/bin/rm -rf .curry
################ end of tests ####################

# Check differences:
DIFF=diff$$
diff TESTRESULT $LOGFILE > $DIFF
if [ "`cat $DIFF`" = "" ] ; then
  echo
  echo "Regression test successfully executed!"
  /bin/rm -f $LOGFILE $DIFF
else
  echo
  echo "Differences in regression test occurred:"
  cat $DIFF
  /bin/rm -f $DIFF
  /bin/mv -f $LOGFILE LOGFILE
  echo "Test output saved in file 'LOGFILE'."
  exit 1
fi
