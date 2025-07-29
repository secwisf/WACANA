import os,sys,subprocess
root="./examples/EOSIO_contracts"
i=0
dirs=os.listdir(root)
# dirs=['pandafun','oracle.new','ramconsumer','pradata','charity','test.token','tokendapppub','tungsten']
print("all count,",len(dirs))
# cmd=f'python3 wana.py -t 200000 -o ./result/addressbook.spthy -e ./examples/EOSIO_contracts/addressbook/addressbook.wasm 2>&1 > ./result/addressbook.txt'
# p=subprocess.Popen(['/bin/bash','-c',cmd])
# print(p.wait(timeout=1200))

for file_name in dirs:
    cmd=f'python3 wana.py -t 3600 -o ./result/{file_name}.spthy -e ./examples/EOSIO_contracts/{file_name}/{file_name}.wasm  > ./result/{file_name}.txt 2>&1'
    print(cmd)
    print(i)
    i+=1
    p=subprocess.Popen(['/bin/bash','-c',cmd])
    try:
        p.wait(3600)
    except:
        continue
