// Part 1: Queue Lock Algorithm for NTHREADS = 2
// Use spin -run -f -m1000000 HW2_1.pml

#define NTHREADS 2

bool queue[NTHREADS] = {1, 0};
byte cnt = 0;

// current number of processes in the critical section 
byte nr_crit_proc = 0;

active [NTHREADS] proctype process() 
{
    byte my_cnt;
    start:
        atomic {
            my_cnt = cnt;
            cnt++;
        }
    try:
        (queue[my_cnt % NTHREADS] == true);
    crit:
        nr_crit_proc++;
        skip;
    leave:
        queue[my_cnt % NTHREADS] = false;
        nr_crit_proc--;
        queue[(my_cnt + 1) % NTHREADS] = true;
    goto start
}

ltl invariant {
    // mutual exclusion
    [] (nr_crit_proc <= 1)

    // flag slots are used in order
    // once queue[0] is 1, it cannot switch to 0 and then 1 again before queue[1] gets set 1
    && [] ((queue[0] == true) -> (!(queue[0] == false && X(queue[0]) == true) U (queue[1] == true)))
    // once queue[1] is 1, it cannot switch to 0 and then 1 again before queue[0] gets set 1
    && [] ((queue[1] == true) -> (!(queue[1] == false && X(queue[1]) == true) U (queue[0] == true)))

    // starvation freedom
    && [](<> (process[0]@crit)) 
    && [](<> (process[1]@crit))
}