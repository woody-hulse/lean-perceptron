import random
import argparse
import numpy as np
from tensorflow.keras.datasets import mnist
import matplotlib.pyplot as plt
from tensorflow.keras.datasets import mnist
from sklearn.cluster import KMeans
from sklearn.metrics import accuracy_score
import umap
from tqdm import tqdm

def load_mnist():
    (x_train, y_train), (x_test, y_test) = mnist.load_data()
    x = np.concatenate([x_train, x_test], axis=0)
    y = np.concatenate([y_train, y_test], axis=0)
    return x, y

def plot_digits(images, labels, n=16, cols=4, cmap="gray"):
    n = min(n, len(images))
    rows = (n + cols - 1) // cols
    plt.figure(figsize=(cols * 2.5, rows * 2.5))
    for i in range(n):
        plt.subplot(rows, cols, i + 1)
        plt.imshow(images[i], cmap=cmap)
        plt.title(f"Label: {labels[i]}")
        plt.axis("off")
    plt.tight_layout()
    plt.show()
    
def plot_digits_umap(images, labels, title="MNIST UMAP Projection"):
    flat_images = images.reshape(len(images), -1)
    reducer = umap.UMAP(n_components=2)
    embedding = reducer.fit_transform(flat_images)

    plt.figure(figsize=(8, 6))
    scatter = plt.scatter(embedding[:, 0], embedding[:, 1], c=labels, cmap='tab10', s=5)
    plt.colorbar(scatter, ticks=range(10))
    plt.title(title)
    plt.xlabel("UMAP Dimension 1")
    plt.ylabel("UMAP Dimension 2")
    plt.show()
    
def linear_separation_kmeans_prune(images, labels):
    flat_images = images.reshape(len(images), -1)
    kmeans = KMeans(n_clusters=10, random_state=42)
    cluster_labels = kmeans.fit_predict(flat_images)

    label_mapping = {}
    for i in range(10):
        mask = (cluster_labels == i)
        if np.sum(mask) == 0:
            continue
        true_labels, counts = np.unique(labels[mask], return_counts=True)
        label_mapping[i] = true_labels[np.argmax(counts)]

    predicted_labels = np.array([label_mapping[cl] for cl in cluster_labels])
    accuracy = accuracy_score(labels, predicted_labels)
    print(f"KMeans clustering accuracy: {accuracy * 100:.2f}%")
    
    correct_mask = (predicted_labels == labels)
    cleaned_images = images[correct_mask]
    cleaned_labels = labels[correct_mask]
    
    cluster_labels = kmeans.fit_predict(cleaned_images.reshape(len(cleaned_images), -1))
    predicted_labels = np.array([label_mapping[cl] for cl in cluster_labels])
    accuracy = accuracy_score(cleaned_labels, predicted_labels)
    print(f"KMeans clustering accuracy after cleaning: {accuracy * 100:.2f}%")
    
    return cleaned_images, cleaned_labels

def train_perceptron_multiclass(X, y, K, epochs=3, W=None):
    N, D = X.shape
    if W is None:
        W = np.zeros((K, D), dtype=np.float32)

    for _ in range(epochs):
        # Shuffle for stability
        idx = np.random.permutation(N)
        for i in idx:
            xi = X[i]
            yi = y[i]
            scores = W @ xi
            pred = np.argmax(scores)
            if pred != yi:
                # Standard perceptron update
                W[yi] += xi
                W[pred] -= xi

    return W


def compute_violations(X, y, W):
    scores = X @ W.T                     # shape (N, K)
    correct = scores[np.arange(len(X)), y]
    margins = scores - correct[:, None]
    margins[np.arange(len(X)), y] = -np.inf
    violations = margins.max(axis=1)
    return violations


def prune_to_linearly_separable(X, y, K, k_remove=10, epochs=1, max_iters=2000):
    X = X.astype(np.float32)
    y = y.astype(np.int32)
    N, D = X.shape

    W = np.zeros((K, D), dtype=np.float32)
    alive = np.arange(N)
    removed = []

    for it in range(max_iters):
        # Warm-start perceptron training
        W = train_perceptron_multiclass(X, y, K, epochs=epochs, W=W)

        # Compute violations
        violations = compute_violations(X, y, W)
        maxv = violations.max()
        print(f"Iter {it}: max violation {maxv:.6f}, remaining {len(X)}")

        # Stopping condition
        if maxv <= 0:
            print("Perfect multiclass linear separability reached.")
            break

        # Remove top-k violators
        k = min(k_remove, len(X))
        worst_indices = np.argpartition(violations, -k)[-k:]
        removed.extend(alive[worst_indices])

        keep_mask = np.ones(len(X), dtype=bool)
        keep_mask[worst_indices] = False

        X = X[keep_mask]
        y = y[keep_mask]
        alive = alive[keep_mask]

    return W, X, y, removed

def print_lean_dataset(name, X, y):
    N, D = X.shape

    print(f"def {name} : Dataset {D} := [")
    for i in range(N):
        feats = ", ".join(str(int(v)) for v in X[i])
        lbl = int(y[i])
        print(f"  {{ features := ![{feats}], label := {lbl} }},")
    print("]")
    

def create_csv_dataset(path, X, y):
    N, D = X.shape
    with open(path, "w") as f:
        for i in range(N):
            feats = ",".join(str(int(v)) for v in X[i])
            lbl = int(y[i])
            f.write(f"{lbl},{feats}\n")

def main():
    parser = argparse.ArgumentParser(description="Load MNIST and plot some digits.")
    parser.add_argument("--num", type=int, default=16, help="Number of digits to plot")
    parser.add_argument("--cols", type=int, default=4, help="Number of columns in the grid")
    args = parser.parse_args()

    x, y = load_mnist()

    idx = np.random.choice(len(x), size=min(args.num, len(x)), replace=False)
    images = x[idx]
    labels = y[idx]

    # plot_digits(images, labels, n=len(idx), cols=args.cols)
    print(f"Old dataset size: {len(x)}")
    # plot_digits_umap(x, y)
    
    # cleaned_images, cleaned_labels = linear_separation_kmeans_prune(x, y)
    # print(f"New dataset size after KMeans filtering: {len(cleaned_images)}")
    # plot_digits_umap(cleaned_images, cleaned_labels, title="MNIST UMAP Projection After KMeans Filtering")
    cleaned_images, cleaned_labels = x, y

    _, pruned_images, pruned_labels, removed_indices = prune_to_linearly_separable(np.reshape(cleaned_images, (len(cleaned_images), -1)), cleaned_labels, K=10, k_remove=1000)
    print(f"New dataset size after multiclass separability pruning: {len(pruned_images)}")
    pruned_images = pruned_images.reshape((len(pruned_images), 28, 28))
    # plot_digits_umap(pruned_images, pruned_labels, title="MNIST UMAP Projection After Multiclass Pruning")
    
    # print_lean_dataset("mnist_pruned", np.reshape(pruned_images, (len(pruned_images), -1))[:1000], pruned_labels[:1000])
    size = 1000
    create_csv_dataset("mnist_pruned.csv", np.reshape(pruned_images[:size], (len(pruned_images[:size]), -1)), pruned_labels[:size])

if __name__ == "__main__":
    main()