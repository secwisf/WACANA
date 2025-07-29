# WACANA: A Concolic Analyzer for Detecting On-chain Data Vulnerabilities in WASM Smart Contracts

# Prerequisites

Install the Docker Python package:

pip install docker

# User Guide

1. Download the image from [this link](https://wacana-data-1329356540.cos.na-ashburn.myqcloud.com/wacana-image.tar)
2. Run multi_run.py

The following parameters can be configured when running:
| Parameter | Description | Default Value |
| ----- | ----- | ---- |
| --data | Directory path of contracts to be analyzed | ./datasets/example |
| --script | Path where WACANA tool is stored |  
| --pnum | Number of concurrent processing threads | 10
| --timeout | Analysis timeout in seconds | 3600


# Example Usage

python multi_run.py --data=./datasets/example --script=/path/to/wacana --pnum=2 --timeout=300


# Benchmark

please refer to WACANA_dataset folder
