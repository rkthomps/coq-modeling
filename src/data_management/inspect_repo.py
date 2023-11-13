import git
import datetime


def get_repo_start_date(repo_path: str) -> datetime.datetime:
    repo = git.Repo(repo_path)
    *_, last = repo.iter_commits()
    return last.committed_datetime
