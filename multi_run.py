import os,sys,subprocess,docker,time
from multiprocessing import Process,Pool

from docker.api import container, volume
from docker.errors import ContainerError

client=docker.from_env()
def p_e(e):
    print("error",e)

def worker(data_dir,name,id,script_dir,timeout):
    if id%20==0:
        client.containers.prune()
    if not os.path.exists(f"rt{id}"):
        os.system(f"mkdir rt{id}")
    
    cmd=f'python3 wana.py -t {timeout} -e {data_dir}/{name}/{name}.wasm -td ./rt{id}/'
    
    print(cmd)
    print(id)
    image_name="wana-docker"
    
    container_output=''
    start_time=time.time()
    try:
        container_output=client.containers.run(image=image_name,working_dir="/wana",command=cmd,volumes={script_dir:{"bind":'/wana','mode':"rw"}},mem_limit="10g",memswap_limit=0,entrypoint="",stderr=True)
    except ContainerError as e:
        container_output=e.container.logs()
        
    end_time=time.time()
    with open(f"./result/{name}.txt","wb") as f:
        f.write(container_output)
    with open(f"./result/{name}_time.txt","w") as f:
        f.write(str(end_time-start_time))
    
def main(dirs,data_dir,script_dir,pnum,timeout):
    client.containers.prune()
    pool=Pool(pnum)

    for i,file_name in enumerate(dirs):
        pool.apply_async(func=worker,args=(data_dir,file_name,i,script_dir,timeout),error_callback=p_e)
    pool.close()
    pool.join()
    print("finished")

if __name__ == "__main__":
    data_dir = "./datasets/example"
    script_dir = ""
    pnum = 10
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
    dirs=os.listdir(data_dir)
    main(dirs,data_dir,script_dir,pnum,timeout)

