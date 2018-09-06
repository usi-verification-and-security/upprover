/* 
 * File:   time_utils.h
 * Author: karinek
 *
 * Created on 23 August 2018, 16:54
 * 
 * Unify interface for time duration of steps
 * 
 * Change once for all location of HiFrog
 * 
 * use:
 * auto solver_start = timestamp();
 * ....
 * auto solver_stop = timestamp();
 * 
 * And report:
 * time_gap(solver_start,solver_stop);
 */

#ifndef TIME_UTILS_H
#define TIME_UTILS_H

#include <ctime>
#include <chrono>

typedef std::chrono::duration<double> timet;

#define timestamp() std::chrono::steady_clock::now()

#define time_gap(stop,start) std::chrono::duration<double>(stop-start).count()

#endif /* TIME_UTILS_H */

