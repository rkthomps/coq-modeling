docker build . --progress=plain -t graph2tac:latest --build-arg display=$DISPLAY
docker run --gpus all -it --name graph2tac --net=host -d graph2tac:latest /bin/bash
