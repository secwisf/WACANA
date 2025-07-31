import os, sys, subprocess, docker, time
from multiprocessing import Pool, Lock



dir_lock = Lock()
client = docker.from_env()

def p_e(e):
    print("Error:", e)

def worker(data_dir, name, id, script_dir, timeout):
    
    rt_dir = f"rt{id}"
    with dir_lock:
        if not os.path.exists(rt_dir):
            os.makedirs(rt_dir, exist_ok=True)
    
    cmd = f'python3 {script_dir}/wana.py -t {timeout} -e {data_dir}/{name}/{name}.wasm -td ./{rt_dir}/'
    print(f"[PID-{os.getpid()}] Processing {name} (ID: {id})")
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd, 
            shell=True,
            stdout=subprocess.PIPE, 
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout + 60  
        )
        output = result.stdout
        if result.returncode != 0:
            output = f"ERROR (exit {result.returncode}):\n{output}"
    except subprocess.TimeoutExpired:
        output = "ERROR: Timeout expired"
    except Exception as e:
        output = f"ERROR: {str(e)}"
    
    end_time = time.time()
    exec_time = end_time - start_time

   
    res_dir = data_dir.replace("/", "_").strip('.')
    with dir_lock:
        os.makedirs(res_dir, exist_ok=True)
    
    
    with open(f"./{res_dir}/{name}.txt", "w") as f:
        f.write(output)
    with open(f"./{res_dir}/{name}_time.txt", "w") as f:
        f.write(str(exec_time))
    
    return id

def main(dirs, data_dir, script_dir, pnum, timeout):
    client.containers.prune()
    
   
    BATCH_SIZE = pnum * 2  
    total = len(dirs)
    completed = 0
    
   
    pool = Pool(pnum)
    
  
    for batch_start in range(0, total, BATCH_SIZE):
        batch = dirs[batch_start:batch_start + BATCH_SIZE]
        print(f"\n=== Processing batch {batch_start//BATCH_SIZE + 1}/{(total-1)//BATCH_SIZE + 1} ===")
        
       
        results = []
        for idx, name in enumerate(batch):
            global_idx = batch_start + idx  
            results.append(
                pool.apply_async(
                    worker, 
                    args=(data_dir, name, global_idx, script_dir, timeout),
                    error_callback=p_e
                )
            )
        
        
        for res in results:
            res.get()  
            completed += 1
            print(f"Progress: {completed}/{total} ({completed/total:.1%})")
    
    pool.close()
    pool.join()
    print("\nAll tasks finished")

if __name__ == "__main__":
    data_dir = "./datasets/example"
    script_dir = ""
    pnum = 5
    timeout = 3600
    args = sys.argv
    print("================setting=========================")
    for arg in args:
        if '--data=' in arg:
            data_dir = arg.split("=")[-1]
            print("Data_dir: your dataset is stored at %s"%data_dir)
        elif "--script=" in arg:
            script_dir = arg.split("=")[-1]
            print("Script_dir: WACANA is stored at %s"%script_dir)
        elif "--pnum=" in arg:
            pnum = int(arg.split("=")[-1])
            print("Process_num: we will use %d processes"%pnum)
        elif "--timeout=" in arg:
            timeout = int(arg.split("=")[-1])
            print("Timeout: the timeout is set to %d"%timeout)
    print("================begin analyzing=========================")
    dirs = os.listdir(data_dir)
    
    dirs = [d for d in dirs 
            if os.path.isdir(os.path.join(data_dir, d)) 
            and os.path.exists(os.path.join(data_dir, d, f"{d}.wasm"))]
    
    main(dirs, data_dir, script_dir, pnum, timeout)
