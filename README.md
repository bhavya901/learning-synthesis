# Learning Synthesis 


### Prerequisites


1. This tool is build on top of Microsoft Ivy which uses Z3 for sat checking. Make sure that you install python binding for Z3 while installing Ivy. Install Ivy from source as binary release provided by them are outdated. For Installation instruction click [here](http://microsoft.github.io/ivy/install.html#source).
```bash
# to test if Ivy is correctly installed run
ivy_check <input_file>
```

2. networkx is used to represent samples as graph. To install you can use the command
```bash
pip install networkx
```

3. Install the python package matplotlib.
```bash
python -mpip install -U matplotlib
```


### Installing

1. Clone the repo in a suitable directory.
```bash
cd ~
git clone https://github.com/bhavya901/learning-synthesis.git
```

2. Ivy installs its source code as a python module. Change your working directory to the path where source code of ivy is located.
```bash
# modify path according to your python2 version. 
cd /usr/local/lib/python2.7/dist-packages/ms_ivy-0.1-py2.7.egg/ivy
``` 

3. replace the files in this directory with files from repository.
```bash
sudo cp -a ~/learning-synthesis/ivy/. ./
```


## Running On programs

Be aware that the tool currently requires the variables used in invariant and conjectures specified in the input program to be of the form <sortName><index>. the sortName should be capitalized and index starts from 0. As an example file ivy/include/semaphore.ivy is provided which is an input file coressponding to client server program. 
You can run on input program by using command below.

```bash
ivy_check <input_file>
```
