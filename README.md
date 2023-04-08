# Spacer on Jupyter

The latest notebook is `Dagstuhl2019.ipynb`.
Open it in your favorite Jupyter notebook server. 
VSCode works quite well for at the moment.


## Setting up venv

```
$ python3 -m venv venv
$ source venv/bin/activate
$ pip install -r requirements.txt
```

Open notebooks in VSCode and pick the virtual environment engine

## Distribution generation instructions

```
python -m build
python3 -m twine upload  dist/* 
```
Use `__token__` as username, and the token from PyPi as password