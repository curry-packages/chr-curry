#!/bin/sh
# Shell script to test the current set of CHR(Curry) examples

# Root location of the Curry System specified by variable CURRYROOT
CURRYROOT=`$CURRYBIN :set v0 :set -time :add Curry.Compiler.Distribution :eval "putStrLn installDir" :quit`
CURRYBINDIR=$CURRYROOT/bin

BACKEND=`$CURRYBIN --noreadline :set v0 :set -time :load Curry.Compiler.Distribution :eval "putStrLn (curryRuntime ++ show curryRuntimeMajorVersion)" :quit 2> /dev/null`

VERBOSE=no
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

if [ "$BACKEND" != sicstus4 -a "$BACKEND" != swi6 -a "$BACKEND" != swi7 -a "$BACKEND" != swi8 ] ; then
  echo "No appropriate Prolog back end, skip the CHR tests."
  exit
fi

LOGFILE=xxx$$
$CURRYBINDIR/cleancurry
cat << EOM | $CURRYBIN -q :set -interactive :set v0 :set printdepth 0 :set -time | tee $LOGFILE
:!echo Loading program Leq
:load Leq
:!echo main10
main10 x        where x free
:!echo main11
main11 (x::Int) y z    where x,y,z free
:!echo main12
main12 (x::Int) y z z' where x,y,z,z' free

:!echo Loading program Bool
:load Bool
:!echo main20
main20 x y z    where x,y,z free
:!echo main21
main21 a b s c  where a,b,s,c free
:!echo main22
main22 a b s c  where a,b,s,c free

:!echo Loading program GCD
:load GCD
:!echo main30
main30
:!echo main31
main31
compileGCD
:!echo Loading program GCDCHR
:load GCDCHR
:!echo solveCHR $ gcdanswer x /\ gcd 206 /\ gcd 40  where x free
solveCHR $ gcdanswer x /\ gcd 206 /\ gcd 40  where x free

:!echo Loading program Fib
:load Fib
:!echo main41
main41 x    where x free
compileFib
:!echo Loading program FIBCHR
:load FIBCHR
:!echo solveCHR $ fib 20 x  where x free
solveCHR $ fib 20 x  where x free

:!echo Loading program FD
:load FD
:!echo main50
main50 x y      where x,y free
:!echo main51
main51 x        where x free
:!echo main52
main52 [x,y,z]  where x,y,z free
:!echo main53
main53 xs       where xs free
:!echo main55
main55 xs       where xs free

:!echo Loading program UnionFind
:load UnionFind
:!echo main60
main60
:!echo main61
main61 x        where x free
:!echo main62
main62 x y      where x,y free
:!echo main63
main63
:!echo main64
main64 x y      where x,y free
:!echo main65
main65 x y      where x,y free
compileUF
:!echo Loading program UFCHR
:load UFCHR
:!echo solveCHR $ andCHR [make 1, make 2, make 3, make 4, make 5, union 1 2, union 3 4, union 5 3, find 2 x, find 4 y]  where x,y free
solveCHR $ andCHR [make 1, make 2, make 3, make 4, make 5, union 1 2, union 3 4, union 5 3, find 2 x, find 4 y]  where x,y free

:!echo Loading program Primes
:load Primes
:!echo main70
main70

:!echo Loading program Gauss
:load Gauss
:!echo main80
main80 x y      where x,y free
:!echo main81
main81 x y      where x,y free
:!echo main82
main82 x y      where x,y free
:!echo main85
main85 i        where i free
:!echo main86
main86 i        where i free

EOM
# clean up:
for p in GCDCHR FIBCHR UFCHR GAUSSCHR ; do
    $CURRYBINDIR/cleancurry $p
    /bin/rm -f $p*
done
################ end of tests ####################
if [ $VERBOSE = yes ] ; then
    cat $LOGFILE
fi
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
