#include <iostream>
#include <vector>
#include <algorithm>
#include <forward_list>
#include <vector>
#include <cstdio>
#include <queue>
#include <random>
#include <ctime>

using namespace std;

struct Minterm;
struct Implicant {  // 蕴含项
	inline Implicant(unsigned int d, unsigned int dc = 0U) :digs(d), dont_care(dc), isPrime(1) {}
	unsigned int digs;
	unsigned int dont_care;
	bool isPrime;

	void Print(int argc) {
		unsigned int mask = 1 << (argc - 1);
		char buffer[100] = { 0 };
		char *cur_char = buffer;
		while (mask) {
			if (mask & digs) {  // '1'
				*cur_char = '1';
				++cur_char;
			} else if (mask & dont_care) {  // '-'
				*cur_char = '-';
				++cur_char;
			} else {
				*cur_char = '0';
				++cur_char;
			}
			mask >>= 1;
		}
		printf("%s ", buffer);
	}
};

struct Minterm {  // 最小项
	inline Minterm(unsigned int d) :digs(d), covered(false) {}
	unsigned int digs;
	bool covered;
	vector<forward_list<Implicant>::iterator> covered_imps;  // 这个最小项被此列表中的本质蕴含项覆盖
};

inline int CountOnes(unsigned int x) {  // 数一个最小项中 1 的个数
	unsigned int mask = 1;
	int counter = 0;
	while (mask) {
		counter += ((x & mask) > 0);
		mask <<= 1;
	}
	return counter;
}

inline bool CanBeCovered(unsigned m, const Implicant &imp) {  // 判断一个最小项是否可以被一个蕴含项覆盖
	return (m & (~imp.dont_care)) == imp.digs;
}

vector<vector<forward_list<Implicant> > > implicants;  // Implicants[无关项个数][1 的个数]
forward_list<Implicant> prime_implicants;  // 本质蕴含项
vector<Minterm> minterms;  // 最小项
vector<vector<Minterm>::iterator> minterms_ptrs;  // 最小项的指针
int cur_min_result_size = 2147483647;  // INF
vector<vector<forward_list<Implicant>::iterator> > results;  // 结果
queue<vector<forward_list<Implicant>::iterator> > result_queue;  // BFS 查找结果时所用的队列
queue<vector<vector<Minterm>::iterator > > minterm_queue;  // 同上
vector<vector<forward_list<Implicant>::iterator> > result_stack;  // DFS 查找结果时所用的栈
vector<vector<vector<Minterm>::iterator > > minterm_stack;  // 同上

void QM(int argc, vector<unsigned int> ms, vector<unsigned int> dcs) {  // 布尔函数的参数数量 & 最小项 & 无关项
	implicants.resize(argc + 1);
	implicants[0].resize(argc + 1);
	implicants[1].resize(argc);

	// 初始化
	for (auto m : ms) {
		implicants[0][CountOnes(m)].emplace_front(m);
		minterms.emplace_back(m);
	}
	for (auto dc : dcs) {
		implicants[0][CountOnes(dc)].emplace_front(dc);
	}

	// 合并蕴含项
	int cur_ones = 0, cur_dcs = 0;
	while (cur_dcs < argc) {
		implicants[cur_dcs + 1].resize(argc - cur_dcs);
		while (cur_ones < argc - cur_dcs) {
			auto &cur_list = implicants[cur_dcs][cur_ones];
			auto &more_one_list = implicants[cur_dcs][cur_ones + 1];  // cur_ones + 1 最大是 argc - cur_dcs, 表示除了 dc 项以外全部是 1
			auto &more_dc_list = implicants[cur_dcs + 1][cur_ones];

			for (auto &m1 : cur_list) {
				for (auto &m2 : more_one_list) {
					unsigned int diff = m2.digs ^ m1.digs;
					if (m1.dont_care == m2.dont_care && CountOnes(diff) == 1) { // 这里没有问题，可合并的情况下 m2 必有且仅有一位比 m1 多 1
						bool flag = true;
						for (auto imp : more_dc_list) {  // 去重
							if (imp.digs == m1.digs && imp.dont_care == (m1.dont_care | diff)) {
								flag = false;
								break;
							}
						}
						if (flag) {
							more_dc_list.emplace_front(m1.digs, (m1.dont_care | diff));
							m1.isPrime = false;
							m2.isPrime = false;
						}
					}
				}
			}
			++cur_ones;
		}
		++cur_dcs;
		cur_ones = 0;
	}

	// 筛选出所有本原蕴含项
	for (auto &imp_list_list : implicants) {
		for (auto &imp_list : imp_list_list) {
			prime_implicants.splice_after(prime_implicants.before_begin(), imp_list);  // 首先把所有此前找到的蕴含项接成一个链表
		}
	}

	int prime_imp_number = 0;
	auto prev_imp_ptr = prime_implicants.begin(); // 由于此列表的生成方式，实际上 PI.begin() 一定是本原蕴含项
	for (auto imp_ptr = prime_implicants.begin(); imp_ptr != prime_implicants.end(); ++imp_ptr) {
		if (!imp_ptr->isPrime) {
			imp_ptr = prev_imp_ptr;
			prime_implicants.erase_after(prev_imp_ptr);  // 把当前的项删掉
		} else {
			prev_imp_ptr = imp_ptr;
			++prime_imp_number;
		}
	}

	// 将每个最小项与能覆盖该最小项的所有本质蕴含项建立对应关系
	for (auto &minterm : minterms) {
		for (auto imp = prime_implicants.begin(); imp != prime_implicants.end(); ++imp) {
			if (CanBeCovered(minterm.digs, *imp)) {
				minterm.covered_imps.push_back(imp);
			}
		}
	}

	// 将最小项按照能够覆盖它的本质蕴含项的数量排序
	sort(minterms.begin(), minterms.end(),
		[](const Minterm &mt1, const Minterm &mt2) {return mt1.covered_imps.size() < mt2.covered_imps.size(); });

	for (auto ptr = minterms.begin(); ptr != minterms.end(); ++ptr) {
		minterms_ptrs.push_back(ptr);
	}

	bool bfs = prime_imp_number < 60;

	if (false) {
		printf("Search Method = BFS\n");
		// 初始化 BFS 的队列
		vector<forward_list<Implicant>::iterator> empty_result;
		result_queue.push(empty_result);
		minterm_queue.push(minterms_ptrs);

		// 用广度优先搜索构建最小覆盖
		printf("Start Search...\n");
		while (!result_queue.empty()) {  // 终止条件是队列为空
			auto result = result_queue.front();  // 从队列中弹出一项
			auto minterms_ptr = minterm_queue.front();
			result_queue.pop();
			minterm_queue.pop();

			if (result.size() > cur_min_result_size) {
				continue;
			}

			if (minterms_ptr.empty()) {  // 如果弹出的覆盖可以完全覆盖所有最小项
				cur_min_result_size = result.size();  // 将最小覆盖的规模设置为此覆盖的规模
				results.push_back(result);   // 在答案中添加此结果
				continue;
			} else if (result.size() == cur_min_result_size) {  // 阻止没有希望的覆盖入队
				continue;
			}

			for (auto next_imp : minterms_ptr.front()->covered_imps) {  // 向 BFS 搜索队列中加入接下来要搜索的路径
				minterm_queue.emplace(minterms_ptr);
				result_queue.emplace(result);
				result_queue.back().push_back(next_imp);  // 向当前搜索路径后添加一个结点
				auto erase_begin = remove_if(minterm_queue.back().begin(), minterm_queue.back().end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // 清除新增的这个结点可以覆盖的所有最小项
				minterm_queue.back().erase(erase_begin, minterm_queue.back().end());
			}
		}
	} else {  // DFS
		printf("Search Method = DFS\n");

		printf("Estimating result size");
		int try_times = 5000 * (min(prime_imp_number, 200));
		srand(clock());
		for (int i = 0; i != try_times; ++i) {  // 随机进行若干次尝试，估计最小覆盖的规模，为 DFS 剪枝
			int cnt = 0;
			auto mt_ptrs = minterms_ptrs;
			while (!mt_ptrs.empty()) {
				auto next_imp = mt_ptrs.front()->covered_imps[rand() % mt_ptrs.front()->covered_imps.size()];
				auto erase_begin = remove_if(mt_ptrs.begin(), mt_ptrs.end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // 清除新增的这个结点可以覆盖的所有最小项
				mt_ptrs.erase(erase_begin, mt_ptrs.end());
				++cnt;
			}
			if (cnt < cur_min_result_size) {
				cur_min_result_size = cnt;
			}
			if (i % 100000 == 0) { printf("."); }  // 增加一点视觉效果..
		}

		// 初始化 DFS 的队列
		vector<forward_list<Implicant>::iterator> empty_result;
		result_stack.push_back(empty_result);
		minterm_stack.push_back(minterms_ptrs);

		// 用深度优先搜索构建最小覆盖
		printf("\nStart Search");
		unsigned int i = 0;
		while (!result_stack.empty()) {  // 终止条件是栈为空
			auto result = result_stack.back();  // 从栈中弹出一项
			auto minterms_ptr = minterm_stack.back();
			result_stack.pop_back();
			minterm_stack.pop_back();

			if (++i % 1000000 == 0) { printf("."); }  // 增加一点视觉效果..

			if (result.size() > cur_min_result_size) {
				continue;
			}

			if (minterms_ptr.empty()) {  // 如果弹出的覆盖可以完全覆盖所有最小项
				if (result.size() < cur_min_result_size) {
					results.clear();
					cur_min_result_size = result.size();  // 将最小覆盖的规模设置为此覆盖的规模
				}
				results.push_back(result);   // 在答案中添加此结果
				continue;
			} else if (result.size() == cur_min_result_size) {  // 阻止没有希望的覆盖入栈
				continue;
			}

			for (auto next_imp : minterms_ptr.front()->covered_imps) {  // 向 DFS 搜索栈中加入接下来要搜索的路径
				minterm_stack.emplace_back(minterms_ptr);
				result_stack.emplace_back(result);
				result_stack.back().push_back(next_imp);  // 向当前搜索路径后添加一个结点
				auto erase_begin = remove_if(minterm_stack.back().begin(), minterm_stack.back().end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // 清除新增的这个结点可以覆盖的所有最小项
				minterm_stack.back().erase(erase_begin, minterm_stack.back().end());
			}
		}
	}
	printf("\n");
}

void PrintResult(int argc) {
	for (auto result : results) {
		for (auto term : result) {
			term->Print(argc);
			printf(" ");
		}
		printf("\n");
	}
}

int main() {
	int argc;
	int minterm_num, dc_num;
	vector<unsigned int> minterms, dcs;

	cout << "Boolean Expression Simplifier by ma-xujie" << endl;
	cout << "Please Input Number Of Boolean Variables:" << endl;
	cin >> argc;
	cout << "Please Input Number Of Minterms:" << endl;
	cin >> minterm_num;
	cout << "Please Input Minterms:" << endl;
	for (int i = 0; i != minterm_num; ++i) {
		unsigned int tmp;
		cin >> tmp;
		minterms.push_back(tmp);
	}
	cout << "Please Input Number Of Don't Care Terms:" << endl;
	cin >> dc_num;
	if (dc_num > 0) {
		cout << "Please Input Don't Care Terms:" << endl;
		for (int i = 0; i != dc_num; ++i) {
			unsigned int tmp;
			cin >> tmp;
			dcs.push_back(tmp);
		}
	}

	QM(argc, minterms, dcs);

	cout << results.size() << " Result(s):" << endl;
	PrintResult(argc);
}