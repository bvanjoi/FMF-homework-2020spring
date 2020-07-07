import os
import time
import multiprocessing as mp
from collections import namedtuple
from datetime import datetime


# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass


Timer = namedtuple('Timer', ('pid', 'time'))


def timer(interval, result):
    for i in range(5):
        time.sleep(interval)
        # TODO: Exercise 4 Code Here
        print( Timer(os.getpid(), time.time()))

if __name__ == '__main__':
    # TODO: Exercise 4: Start two timers which record time with different
    # intervals, use Queue or SimpleQueue to gather the result.
    #
    # example output:
    #
    # Timer(pid=39834, time='2020-06-15 05:39:07.986')
    # Timer(pid=39835, time='2020-06-15 05:39:08.988')
    # Timer(pid=39834, time='2020-06-15 05:39:08.990')
    # Timer(pid=39834, time='2020-06-15 05:39:09.993')
    # Timer(pid=39835, time='2020-06-15 05:39:10.993')
    # Timer(pid=39834, time='2020-06-15 05:39:10.996')
    # Timer(pid=39834, time='2020-06-15 05:39:11.999')
    # Timer(pid=39835, time='2020-06-15 05:39:12.997')
    # Timer(pid=39835, time='2020-06-15 05:39:15.001')
    # Timer(pid=39835, time='2020-06-15 05:39:17.005')
    #
    p = mp.Process( target=timer, args=(1,''))
    p.start()
    timer(1,'')
    p.join()