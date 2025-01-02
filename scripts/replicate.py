



import argparse

def replicate_tab1():
    print("hi")
    pass

def replicate_tab2():
    pass

def replicate_tab3():
    pass

def replicate_tab4():
    pass

def replicate_tab5():
    pass

def replicate_tab6():
    pass

def replicate_tab7():
    pass

def replicate_tab8():
    pass

def replicate_tab9():
    pass

def replicate_tab10():
    pass

def replicate_fig2():
    pass

def replicate_fig3():
    pass

def replicate_fig4():
    pass

def replicate_fig5():
    pass

def replicate_fig6():
    pass

OPTIONS = {
    "tab1": replicate_tab1,
    "tab2": replicate_tab2, 
    "tab3": replicate_tab3,
    "tab4": replicate_tab4,
    "tab5": replicate_tab5,
    "tab6": replicate_tab6,
    "tab7": replicate_tab7,
    "tab8": replicate_tab8,
    "tab9": replicate_tab9,
    "tab10": replicate_tab10,
    "fig2": replicate_fig2,
    "fig3": replicate_fig3,
    "fig4": replicate_fig4,
    "fig5": replicate_fig5,
    "fig6": replicate_fig6,
}



if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Replicate Rango Results.")

    for k, _ in OPTIONS.items():
        parser.add_argument(f"--{k}", action="store_true", help=f"Replicate {k}")

    args = parser.parse_args()

    for k, v in args.__dict__.items():
        if v:
            OPTIONS[k]()
            break
