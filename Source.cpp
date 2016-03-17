#include <iostream>
#include <vector>
#include <algorithm>
#include <forward_list>
#include <vector>
#include <cstdio>
#include <queue>
#include <random>

using namespace std;

struct Minterm;
struct Implicant {  // 蕴含项
	inline Implicant(unsigned int d, unsigned int dc = 0U) :digs(d), dont_care(dc), isPrime(1) {}
	unsigned int digs;
	unsigned int dont_care;
	bool isPrime;

	void Print(int argc) {  // 测试用
		unsigned int mask = 1 << (argc - 1);
		char output_ch = 'A';
		char buffer[100] = { 0 };
		char *cur_char = buffer;
		while (mask) {
			if (mask & digs) {  // '1'
				*cur_char = output_ch++;
				++cur_char;
			} else if (mask & dont_care) {  // '-'
				// *cur_char = '-';
			} else {
				*cur_char = output_ch++;
				++cur_char;
				*cur_char = '\'';
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
int min_cover_imps = 2147483647;  // INF
vector<vector<forward_list<Implicant>::iterator> > results;  // 结果
queue<vector<forward_list<Implicant>::iterator> > result_queue;  // BFS 查找结果时所用的队列
queue<vector<vector<Minterm>::iterator > > minterm_queue;  // 同上

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

	auto prev_imp_ptr = prime_implicants.begin(); // 由于此列表的生成方式，实际上 PI.begin() 一定是本原蕴含项
	for (auto imp_ptr = prime_implicants.begin(); imp_ptr != prime_implicants.end(); ++imp_ptr) {
		if (!imp_ptr->isPrime) {
			imp_ptr = prev_imp_ptr;
			prime_implicants.erase_after(prev_imp_ptr);  // 把当前的项删掉
		} else {
			prev_imp_ptr = imp_ptr;
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

	// 初始化 BFS 的队列
	vector<forward_list<Implicant>::iterator> empty_result;
	result_queue.push(empty_result);
	minterm_queue.push(minterms_ptrs);

	// 用广度优先搜索构建最小覆盖
	while (!result_queue.empty()) {  // 终止条件是队列为空
		auto result = result_queue.front();  // 从队列中弹出一项
		auto minterms_ptr = minterm_queue.front();
		result_queue.pop();
		minterm_queue.pop();

		if (result.size() > min_cover_imps) {
			continue;
		}

		if (minterms_ptr.empty()) {  // 如果弹出的覆盖可以完全覆盖所有最小项
			min_cover_imps = result.size();  // 将最小覆盖的规模设置为此覆盖的规模
			results.push_back(result);   // 在答案中添加此结果
			continue;
		} else if (result.size() == min_cover_imps) {  // 阻止没有希望的覆盖入队
			continue;
		}
		if (result_queue.size() > 2000000) {  // 为避免运行后爆栈而无法产生结果，此处对搜索队列的长度做了限制。所以如果最终结果的搜索量大于此界限的时候有可能无法输出所有结果，或者结果并非最小覆盖
			// printf("WARNING!\n");
			continue;
		}
		for (auto next_imp : minterms_ptr.front()->covered_imps) {  // 向 BST 搜索队列中加入接下来要搜索的路径
			minterm_queue.emplace(minterms_ptr);
			result_queue.emplace(result);
			result_queue.back().push_back(next_imp);  // 向当前搜索路径后添加一个结点
			auto erase_begin = remove_if(minterm_queue.back().begin(), minterm_queue.back().end(),
				[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // 清除新增的这个结点可以覆盖的所有最小项
			minterm_queue.back().erase(erase_begin, minterm_queue.back().end());
		}
	}
}

int main() {
	// QM(2, { 0, 1, 2, 3 }, {});
	// QM(3, { 0, 4, 5, 7 }, {});
	// QM(4, { 1, 3, 4, 5, 6, 10, 11, 13, 14, 15 }, {});
	vector<unsigned int> tmp;
	vector<unsigned int> dc;
	for (unsigned int i = 0; i != 1000; ++i) {
		if (rand() % 10 == 0) {
			tmp.push_back(i);
		} else if (rand() % 20 == 0) {
			dc.push_back(i);
		}
	}
	QM(10, tmp, dc);
	for (auto x : results) {
		for (auto t : x) {
			t->Print(10);
		}
		printf("\n");
	}
}