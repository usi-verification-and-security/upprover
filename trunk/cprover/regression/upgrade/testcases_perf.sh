
echo CHECKING TWO VERSIONS: floppy A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/floppy_a0.c
echo CHECKING TWO VERSIONS floppy A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/floppy_a1.c ./testcases_perf/floppy_a0.c



echo CHECKING TWO VERSIONS floppy A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/floppy_a1.c
echo CHECKING TWO VERSIONS floppy A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/floppy_a2.c ./testcases_perf/floppy_a1.c





echo Lets check Kbfiltr

echo CHECKING TWO VERSIONS kbfiltr A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/kbfiltr_a0.c
echo CHECKING TWO VERSIONS kbfiltr A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/kbfiltr_a1.c ./testcases_perf/kbfiltr_a0.c



echo CHECKING TWO VERSIONS kbfiltr A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/kbfiltr_a1.c
echo CHECKING TWO VERSIONS kbfiltr A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/kbfiltr_a2.c ./testcases_perf/kbfiltr_a1.c





echo Lets check diskperf

echo CHECKING TWO VERSIONS diskperf A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/diskperf_a0.c
echo CHECKING TWO VERSIONS diskperf A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/diskperf_a1.c ./testcases_perf/diskperf_a0.c


echo CHECKING TWO VERSIONS diskperf A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 1 --logic qflra ./testcases_perf/diskperf_a1.c
echo CHECKING TWO VERSIONS diskperf A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 1 --logic qflra --do-upgrade-check ./testcases_perf/diskperf_a2.c ./testcases_perf/diskperf_a1.c


