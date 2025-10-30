#!/usr/bin/env python3

import time
import psutil
import os
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing

def test_cpu_bound_task(task_id):
    """Simulate CPU-intensive work"""
    start_time = time.time()
    # CPU-bound computation
    result = sum(x*x for x in range(200000))
    duration = time.time() - start_time
    return task_id, duration, os.getpid(), result

def test_io_bound_task(task_id):
    """Simulate I/O-intensive work (like file reading)"""
    start_time = time.time()
    # Simulate file I/O
    with open('/tmp/test_file.txt', 'w') as f:
        f.write('x' * 10000)
    with open('/tmp/test_file.txt', 'r') as f:
        data = f.read()
    os.remove('/tmp/test_file.txt')
    duration = time.time() - start_time
    return task_id, duration, os.getpid(), len(data)

def run_parallelism_test():
    print(f"System Info:")
    print(f"  CPU cores: {psutil.cpu_count(logical=False)} physical, {psutil.cpu_count(logical=True)} logical")
    print(f"  Available memory: {psutil.virtual_memory().available / (1024**3):.1f} GB")
    print(f"  Python multiprocessing CPU count: {multiprocessing.cpu_count()}")
    
    # Test CPU-bound parallelism
    print(f"\n=== CPU-Bound Task Test ===")
    num_tasks = 20
    max_workers = 10
    
    # Sequential baseline
    print("Running sequential baseline...")
    start_time = time.time()
    sequential_results = [test_cpu_bound_task(i) for i in range(num_tasks)]
    sequential_time = time.time() - start_time
    print(f"Sequential time: {sequential_time:.2f}s")
    
    # Parallel test
    print(f"Running parallel with {max_workers} workers...")
    start_time = time.time()
    pids_used = set()
    
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(test_cpu_bound_task, i) for i in range(num_tasks)]
        parallel_results = []
        for future in as_completed(futures):
            task_id, duration, pid, result = future.result()
            parallel_results.append((task_id, duration, pid, result))
            pids_used.add(pid)
            print(f"  Task {task_id:2d}: {duration:.3f}s on PID {pid}")
    
    parallel_time = time.time() - start_time
    speedup = sequential_time / parallel_time
    efficiency = speedup / max_workers
    
    print(f"\nResults:")
    print(f"  Parallel time: {parallel_time:.2f}s")
    print(f"  Speedup: {speedup:.1f}x")
    print(f"  Efficiency: {efficiency:.1f} ({efficiency*100:.0f}%)")
    print(f"  Processes used: {len(pids_used)}")
    print(f"  Expected ideal time: {sequential_time/max_workers:.2f}s")
    
    # Test I/O-bound parallelism
    print(f"\n=== I/O-Bound Task Test ===")
    print("Running I/O-bound parallel test...")
    start_time = time.time()
    pids_used = set()
    
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(test_io_bound_task, i) for i in range(num_tasks)]
        for future in as_completed(futures):
            task_id, duration, pid, result = future.result()
            pids_used.add(pid)
            print(f"  I/O Task {task_id:2d}: {duration:.3f}s on PID {pid}")
    
    io_parallel_time = time.time() - start_time
    print(f"I/O parallel time: {io_parallel_time:.2f}s")
    print(f"I/O processes used: {len(pids_used)}")

if __name__ == "__main__":
    run_parallelism_test()
