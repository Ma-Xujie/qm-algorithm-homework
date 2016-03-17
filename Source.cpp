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
struct Implicant {  // �̺���
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

struct Minterm {  // ��С��
	inline Minterm(unsigned int d) :digs(d), covered(false) {}
	unsigned int digs;
	bool covered;
	vector<forward_list<Implicant>::iterator> covered_imps;  // �����С����б��еı����̺����
};

inline int CountOnes(unsigned int x) {  // ��һ����С���� 1 �ĸ���
	unsigned int mask = 1;
	int counter = 0;
	while (mask) {
		counter += ((x & mask) > 0);
		mask <<= 1;
	}
	return counter;
}

inline bool CanBeCovered(unsigned m, const Implicant &imp) {  // �ж�һ����С���Ƿ���Ա�һ���̺����
	return (m & (~imp.dont_care)) == imp.digs;
}

vector<vector<forward_list<Implicant> > > implicants;  // Implicants[�޹������][1 �ĸ���]
forward_list<Implicant> prime_implicants;  // �����̺���
vector<Minterm> minterms;  // ��С��
vector<vector<Minterm>::iterator> minterms_ptrs;  // ��С���ָ��
int cur_min_result_size = 2147483647;  // INF
vector<vector<forward_list<Implicant>::iterator> > results;  // ���
queue<vector<forward_list<Implicant>::iterator> > result_queue;  // BFS ���ҽ��ʱ���õĶ���
queue<vector<vector<Minterm>::iterator > > minterm_queue;  // ͬ��
vector<vector<forward_list<Implicant>::iterator> > result_stack;  // DFS ���ҽ��ʱ���õ�ջ
vector<vector<vector<Minterm>::iterator > > minterm_stack;  // ͬ��

void QM(int argc, vector<unsigned int> ms, vector<unsigned int> dcs) {  // ���������Ĳ������� & ��С�� & �޹���
	implicants.resize(argc + 1);
	implicants[0].resize(argc + 1);
	implicants[1].resize(argc);

	// ��ʼ��
	for (auto m : ms) {
		implicants[0][CountOnes(m)].emplace_front(m);
		minterms.emplace_back(m);
	}
	for (auto dc : dcs) {
		implicants[0][CountOnes(dc)].emplace_front(dc);
	}

	// �ϲ��̺���
	int cur_ones = 0, cur_dcs = 0;
	while (cur_dcs < argc) {
		implicants[cur_dcs + 1].resize(argc - cur_dcs);
		while (cur_ones < argc - cur_dcs) {
			auto &cur_list = implicants[cur_dcs][cur_ones];
			auto &more_one_list = implicants[cur_dcs][cur_ones + 1];  // cur_ones + 1 ����� argc - cur_dcs, ��ʾ���� dc ������ȫ���� 1
			auto &more_dc_list = implicants[cur_dcs + 1][cur_ones];

			for (auto &m1 : cur_list) {
				for (auto &m2 : more_one_list) {
					unsigned int diff = m2.digs ^ m1.digs;
					if (m1.dont_care == m2.dont_care && CountOnes(diff) == 1) { // ����û�����⣬�ɺϲ�������� m2 �����ҽ���һλ�� m1 �� 1
						bool flag = true;
						for (auto imp : more_dc_list) {  // ȥ��
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

	// ɸѡ�����б�ԭ�̺���
	for (auto &imp_list_list : implicants) {
		for (auto &imp_list : imp_list_list) {
			prime_implicants.splice_after(prime_implicants.before_begin(), imp_list);  // ���Ȱ����д�ǰ�ҵ����̺���ӳ�һ������
		}
	}

	int prime_imp_number = 0;
	auto prev_imp_ptr = prime_implicants.begin(); // ���ڴ��б�����ɷ�ʽ��ʵ���� PI.begin() һ���Ǳ�ԭ�̺���
	for (auto imp_ptr = prime_implicants.begin(); imp_ptr != prime_implicants.end(); ++imp_ptr) {
		if (!imp_ptr->isPrime) {
			imp_ptr = prev_imp_ptr;
			prime_implicants.erase_after(prev_imp_ptr);  // �ѵ�ǰ����ɾ��
		} else {
			prev_imp_ptr = imp_ptr;
			++prime_imp_number;
		}
	}

	// ��ÿ����С�����ܸ��Ǹ���С������б����̺������Ӧ��ϵ
	for (auto &minterm : minterms) {
		for (auto imp = prime_implicants.begin(); imp != prime_implicants.end(); ++imp) {
			if (CanBeCovered(minterm.digs, *imp)) {
				minterm.covered_imps.push_back(imp);
			}
		}
	}

	// ����С����ܹ��������ı����̺������������
	sort(minterms.begin(), minterms.end(),
		[](const Minterm &mt1, const Minterm &mt2) {return mt1.covered_imps.size() < mt2.covered_imps.size(); });

	for (auto ptr = minterms.begin(); ptr != minterms.end(); ++ptr) {
		minterms_ptrs.push_back(ptr);
	}

	bool bfs = prime_imp_number < 60;

	if (false) {
		printf("Search Method = BFS\n");
		// ��ʼ�� BFS �Ķ���
		vector<forward_list<Implicant>::iterator> empty_result;
		result_queue.push(empty_result);
		minterm_queue.push(minterms_ptrs);

		// �ù����������������С����
		printf("Start Search...\n");
		while (!result_queue.empty()) {  // ��ֹ�����Ƕ���Ϊ��
			auto result = result_queue.front();  // �Ӷ����е���һ��
			auto minterms_ptr = minterm_queue.front();
			result_queue.pop();
			minterm_queue.pop();

			if (result.size() > cur_min_result_size) {
				continue;
			}

			if (minterms_ptr.empty()) {  // ��������ĸ��ǿ�����ȫ����������С��
				cur_min_result_size = result.size();  // ����С���ǵĹ�ģ����Ϊ�˸��ǵĹ�ģ
				results.push_back(result);   // �ڴ�����Ӵ˽��
				continue;
			} else if (result.size() == cur_min_result_size) {  // ��ֹû��ϣ���ĸ������
				continue;
			}

			for (auto next_imp : minterms_ptr.front()->covered_imps) {  // �� BFS ���������м��������Ҫ������·��
				minterm_queue.emplace(minterms_ptr);
				result_queue.emplace(result);
				result_queue.back().push_back(next_imp);  // ��ǰ����·�������һ�����
				auto erase_begin = remove_if(minterm_queue.back().begin(), minterm_queue.back().end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �����������������Ը��ǵ�������С��
				minterm_queue.back().erase(erase_begin, minterm_queue.back().end());
			}
		}
	} else {  // DFS
		printf("Search Method = DFS\n");

		printf("Estimating result size");
		int try_times = 5000 * (min(prime_imp_number, 200));
		srand(clock());
		for (int i = 0; i != try_times; ++i) {  // ����������ɴγ��ԣ�������С���ǵĹ�ģ��Ϊ DFS ��֦
			int cnt = 0;
			auto mt_ptrs = minterms_ptrs;
			while (!mt_ptrs.empty()) {
				auto next_imp = mt_ptrs.front()->covered_imps[rand() % mt_ptrs.front()->covered_imps.size()];
				auto erase_begin = remove_if(mt_ptrs.begin(), mt_ptrs.end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �����������������Ը��ǵ�������С��
				mt_ptrs.erase(erase_begin, mt_ptrs.end());
				++cnt;
			}
			if (cnt < cur_min_result_size) {
				cur_min_result_size = cnt;
			}
			if (i % 100000 == 0) { printf("."); }  // ����һ���Ӿ�Ч��..
		}

		// ��ʼ�� DFS �Ķ���
		vector<forward_list<Implicant>::iterator> empty_result;
		result_stack.push_back(empty_result);
		minterm_stack.push_back(minterms_ptrs);

		// �������������������С����
		printf("\nStart Search");
		unsigned int i = 0;
		while (!result_stack.empty()) {  // ��ֹ������ջΪ��
			auto result = result_stack.back();  // ��ջ�е���һ��
			auto minterms_ptr = minterm_stack.back();
			result_stack.pop_back();
			minterm_stack.pop_back();

			if (++i % 1000000 == 0) { printf("."); }  // ����һ���Ӿ�Ч��..

			if (result.size() > cur_min_result_size) {
				continue;
			}

			if (minterms_ptr.empty()) {  // ��������ĸ��ǿ�����ȫ����������С��
				if (result.size() < cur_min_result_size) {
					results.clear();
					cur_min_result_size = result.size();  // ����С���ǵĹ�ģ����Ϊ�˸��ǵĹ�ģ
				}
				results.push_back(result);   // �ڴ�����Ӵ˽��
				continue;
			} else if (result.size() == cur_min_result_size) {  // ��ֹû��ϣ���ĸ�����ջ
				continue;
			}

			for (auto next_imp : minterms_ptr.front()->covered_imps) {  // �� DFS ����ջ�м��������Ҫ������·��
				minterm_stack.emplace_back(minterms_ptr);
				result_stack.emplace_back(result);
				result_stack.back().push_back(next_imp);  // ��ǰ����·�������һ�����
				auto erase_begin = remove_if(minterm_stack.back().begin(), minterm_stack.back().end(),
					[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �����������������Ը��ǵ�������С��
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