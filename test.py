import json
import os,sys,subprocess,docker
from multiprocessing import Process,Pool

from docker.api import container, volume
from docker.errors import ContainerError
# from docker import Client
# with open("./rt/log7.txt","r") as f:
#     res=json.load(f)

# with open("./log7.txt","w") as f:
#     f.write('\n'.join(map(str,res)))

client=docker.from_env()
try:
    client.containers.run("python:latest", "python -c 'print(123); exit(1)'")
except ContainerError as exc:
    print(exc.container.logs())
