
echo CHECKING TWO VERSIONS: floppy A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing  --logic prop ./testcases_perf/floppy_a0.c
echo CHECKING TWO VERSIONS floppy A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing  --logic prop --do-upgrade-check ./testcases_perf/floppy_a1.c ./testcases_perf/floppy_a0.c

echo CHECKING TWO VERSIONS floppy A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing  --logic prop ./testcases_perf/floppy_a1.c
echo CHECKING TWO VERSIONS floppy A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing  --logic prop --do-upgrade-check ./testcases_perf/floppy_a2.c ./testcases_perf/floppy_a1.c


echo CHECKING TWO VERSIONS floppy B0, B1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing  --logic prop ./testcases_perf/floppy_b0.c 
echo CHECKING TWO VERSIONS floppy B0, B1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing  --logic prop --do-upgrade-check ./testcases_perf/floppy_b1.c ./testcases_perf/floppy_b0.c

echo CHECKING TWO VERSIONS floppy B1, B2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --logic prop ./testcases_perf/floppy_b1.c
echo CHECKING TWO VERSIONS floppy B1, B2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --logic prop --do-upgrade-check ./testcases_perf/floppy_b2.c ./testcases_perf/floppy_b1.c


echo CHECKING TWO VERSIONS floppy C0, C1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing  --logic prop ./testcases_perf/floppy_c0.c 
echo CHECKING TWO VERSIONS floppy C0, C1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --logic prop --do-upgrade-check ./testcases_perf/floppy_c1.c ./testcases_perf/floppy_c0.c

echo CHECKING TWO VERSIONS floppy C1, C2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --logic prop ./testcases_perf/floppy_c1.c
echo CHECKING TWO VERSIONS floppy C1, C2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing  --logic prop --do-upgrade-check ./testcases_perf/floppy_c2.c ./testcases_perf/floppy_c1.c

echo CHECKING TWO VERSIONS floppy D0, D1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 6 --logic prop ./testcases_perf/floppy_d0.c 
echo CHECKING TWO VERSIONS floppy D0, D1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 6 --logic prop --do-upgrade-check ./testcases_perf/floppy_d1.c ./testcases_perf/floppy_d0.c

echo CHECKING TWO VERSIONS floppy D1, D2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 4 --logic prop ./testcases_perf/floppy_d1.c
echo CHECKING TWO VERSIONS floppy D1, D2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 4 --logic prop --do-upgrade-check ./testcases_perf/floppy_d2.c ./testcases_perf/floppy_d1.c





echo Lets check Kbfiltr

echo CHECKING TWO VERSIONS kbfiltr A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --logic prop ./testcases_perf/kbfiltr_a0.c
echo CHECKING TWO VERSIONS kbfiltr A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing  --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_a1.c ./testcases_perf/kbfiltr_a0.c

echo CHECKING TWO VERSIONS kbfiltr A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/kbfiltr_a1.c
echo CHECKING TWO VERSIONS kbfiltr A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_a2.c ./testcases_perf/kbfiltr_a1.c


echo CHECKING TWO VERSIONS kbfiltr B0, B1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/kbfiltr_b0.c 
echo CHECKING TWO VERSIONS kbfiltr B0, B1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_b1.c ./testcases_perf/kbfiltr_b0.c

echo CHECKING TWO VERSIONS kbfiltr B1, B2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/kbfiltr_b1.c
echo CHECKING TWO VERSIONS kbfiltr B1, B2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_b2.c ./testcases_perf/kbfiltr_b1.c


echo CHECKING TWO VERSIONS kbfiltr C0, C1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/kbfiltr_c0.c 
echo CHECKING TWO VERSIONS kbfiltr C0, C1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_c1.c ./testcases_perf/kbfiltr_c0.c

echo CHECKING TWO VERSIONS kbfiltr C1, C2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/kbfiltr_c1.c
echo CHECKING TWO VERSIONS kbfiltr C1, C2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_c2.c ./testcases_perf/kbfiltr_c1.c

echo CHECKING TWO VERSIONS kbfiltr D0, D1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 10 --logic prop ./testcases_perf/kbfiltr_d0.c 
echo CHECKING TWO VERSIONS kbfiltr D0, D1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 10 --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_d1.c ./testcases_perf/kbfiltr_d0.c

echo CHECKING TWO VERSIONS kbfiltr D1, D2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing --unwind 10 --logic prop ./testcases_perf/kbfiltr_d1.c
echo CHECKING TWO VERSIONS kbfiltr D1, D2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing --unwind 10 --logic prop --do-upgrade-check ./testcases_perf/kbfiltr_d2.c ./testcases_perf/kbfiltr_d1.c






echo Lets check diskperf

echo CHECKING TWO VERSIONS diskperf A0, A1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_a0.c
echo CHECKING TWO VERSIONS diskperf A0, A1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_a1.c ./testcases_perf/diskperf_a0.c

echo CHECKING TWO VERSIONS diskperf A1, A2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_a1.c
echo CHECKING TWO VERSIONS diskperf A1, A2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_a2.c ./testcases_perf/diskperf_a1.c


echo CHECKING TWO VERSIONS diskperf B0, B1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_b0.c 
echo CHECKING TWO VERSIONS diskperf B0, B1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_b1.c ./testcases_perf/diskperf_b0.c

echo CHECKING TWO VERSIONS diskperf B1, B2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_b1.c
echo CHECKING TWO VERSIONS diskperf B1, B2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_b2.c ./testcases_perf/diskperf_b1.c


echo CHECKING TWO VERSIONS diskperf C0, C1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_c0.c 
echo CHECKING TWO VERSIONS diskperf C0, C1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_c1.c ./testcases_perf/diskperf_c0.c

echo CHECKING TWO VERSIONS diskperf C1, C2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_c1.c
echo CHECKING TWO VERSIONS diskperf C1, C2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_c2.c ./testcases_perf/diskperf_c1.c

echo CHECKING TWO VERSIONS diskperf D0, D1
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_d0.c 
echo CHECKING TWO VERSIONS diskperf D0, D1
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_d1.c ./testcases_perf/diskperf_d0.c

echo CHECKING TWO VERSIONS diskperf D1, D2
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --init-upgrade-check --no-slicing   --logic prop ./testcases_perf/diskperf_d1.c
echo CHECKING TWO VERSIONS diskperf D1, D2
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --no-slicing   --logic prop --do-upgrade-check ./testcases_perf/diskperf_d2.c ./testcases_perf/diskperf_d1.c




echo lets check VTT_A

echo CHECKING TWO VERSIONS P2P_Joints_TG3_e_nh2.c P2P_Joints_TG3_e_nh3.c
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing ./testcases_perf/P2P_Joints_TG3_e_nh2.c
echo CHECKING TWO VERSIONS P2P_Joints_TG3_e_nh2.c P2P_Joints_TG3_e_nh3.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG3_e_nh3.c   --no-slicing  ./testcases_perf/P2P_Joints_TG3_e_nh2.c


rm __summaries __omega
echo CHECKING TWO VERSIONS P2P_Joints_TG3_e_nh3.c P2P_Joints_TG3_e_nh4.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing    ./testcases_perf/P2P_Joints_TG3_e_nh3.c
echo CHECKING TWO VERSIONS P2P_Joints_TG3_e_nh3.c P2P_Joints_TG3_e_nh4.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG3_e_nh4.c   --no-slicing  ./testcases_perf/P2P_Joints_TG3_e_nh3.c







echo lets check VTT_C

echo CHECKING TWO VERSIONS  P2P_Joints_TG4_1.c P2P_Joints_TG4_2.c
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing  ./testcases_perf/P2P_Joints_TG4_1.c
echo CHECKING TWO VERSIONS  P2P_Joints_TG4_1.c P2P_Joints_TG4_2.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG4_2.c --no-slicing  ./testcases_perf/P2P_Joints_TG4_1.c

echo CHECKING TWO VERSIONS P2P_Joints_TG4_2.c P2P_Joints_TG4_3.c 
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing   ./testcases_perf/P2P_Joints_TG4_2.c
echo CHECKING TWO VERSIONS P2P_Joints_TG4_2.c P2P_Joints_TG4_3.c 
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG4_3.c --no-slicing  ./testcases_perf/P2P_Joints_TG4_2.c





echo lets check VTT_D

echo CHECKING TWO VERSIONS P2P_Joints_TG4_long_1.c P2P_Joints_TG4_long_2.c
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing  ./testcases_perf/P2P_Joints_TG4_long_1.c
echo CHECKING TWO VERSIONS P2P_Joints_TG4_long_1.c P2P_Joints_TG4_long_2.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG4_long_2.c  --no-slicing  ./testcases_perf/P2P_Joints_TG4_long_1.c

echo CHECKING TWO VERSIONS  P2P_Joints_TG4_long_2.c P2P_Joints_TG4_long_3.c
rm __summaries __omega
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --init-upgrade-check --no-slicing  ./testcases_perf/P2P_Joints_TG4_long_2.c
echo CHECKING TWO VERSIONS  P2P_Joints_TG4_long_2.c P2P_Joints_TG4_long_3.c
ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ./hifrog --logic prop  --do-upgrade-check  ./testcases_perf/P2P_Joints_TG4_long_3.c --no-slicing  ./testcases_perf/P2P_Joints_TG4_long_2.c





