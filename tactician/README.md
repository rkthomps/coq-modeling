Note: Run from the tactician folder.

```
cp -r ../raw-data/coq-dataset/data_points data_points
cp -r ../raw-data/coq-dataset/sentences.db sentences.db
docker build . --progress=plain -t graph2tac:latest --build-arg git_token=<GITHUB_ACCESS_TOKEN>
docker run --gpus all -it --name graph2tac --net=host -d graph2tac:latest /bin/bash
```
