#include "service.hpp"
#include <cocaine/messages.hpp>

#define debug() if (1) {} else std::cerr
//#define debug() std::cerr << __PRETTY_FUNCTION__ << ": " << __LINE__ << " "

namespace cocaine {

using namespace std::placeholders;

elliptics_service_t::elliptics_service_t(context_t &context, io::reactor_t &reactor, const std::string &name, const Json::Value &args) :
	api::service_t(context, reactor, name, args),
	m_storage(api::storage(context, args.get("source", "core").asString())),
	m_elliptics(dynamic_cast<storage::elliptics_storage_t*>(m_storage.get()))
{
	debug() << m_elliptics << std::endl;

	if (!m_elliptics) {
		throw error_t("To use elliptics service storage must be also elliptics");
	}

	on<io::storage::read  >("read",   std::bind(&elliptics_service_t::read,   this, _1, _2));
	on<io::storage::write >("write",  std::bind(&elliptics_service_t::write,  this, _1, _2, _3, _4));
	on<io::storage::remove>("remove", std::bind(&elliptics_service_t::remove, this, _1, _2));
	on<io::storage::find  >("find",   std::bind(&elliptics_service_t::find,   this, _1, _2));
	on<elliptics::cache_read >("cache_read",  std::bind(&elliptics_service_t::cache_read,  this, _1, _2));
	on<elliptics::cache_write>("cache_write", std::bind(&elliptics_service_t::cache_write, this, _1, _2, _3, _4));
	on<elliptics::bulk_read  >("bulk_read",   std::bind(&elliptics_service_t::bulk_read,   this, _1, _2));
}

deferred<std::string> elliptics_service_t::read(const std::string &collection, const std::string &key)
{
	debug() << "read, collection: " << collection << ", key: " << key << std::endl;
	deferred<std::string> promise;

	m_elliptics->async_read(collection, key).connect(std::bind(&elliptics_service_t::on_read_completed,
		promise, _1, _2));

	return promise;
}

deferred<void> elliptics_service_t::write(const std::string &collection, const std::string &key, const std::string &blob, const std::vector<std::string> &tags)
{
	debug() << "write, collection: " << collection << ", key: " << key << std::endl;
	deferred<void> promise;

	m_elliptics->async_write(collection, key, blob, tags).connect(std::bind(&elliptics_service_t::on_write_completed,
		promise, _1, _2));

	return promise;
}

deferred<std::vector<std::string> > elliptics_service_t::find(const std::string &collection, const std::vector<std::string> &tags)
{
	debug() << "lits, collection: " << collection << std::endl;
	deferred<std::vector<std::string> > promise;

	m_elliptics->async_find(collection, tags).connect(std::bind(&elliptics_service_t::on_find_completed,
		promise, _1, _2));

	return promise;
}

deferred<void> elliptics_service_t::remove(const std::string &collection, const std::string &key)
{
	debug() << "remove, collection: " << collection << ", key: " << key << std::endl;
	deferred<void> promise;

	m_elliptics->async_remove(collection, key).connect(std::bind(&elliptics_service_t::on_remove_completed,
		promise, _1, _2));

	return promise;
}

deferred<std::string> elliptics_service_t::cache_read(const std::string &collection, const std::string &key)
{
	deferred<std::string> promise;

	m_elliptics->async_cache_read(collection, key).connect(std::bind(&elliptics_service_t::on_read_completed,
		promise, _1, _2));

	return promise;
}

deferred<void> elliptics_service_t::cache_write(const std::string &collection, const std::string &key,
	const std::string &blob, int timeout)
{
	deferred<void> promise;

	m_elliptics->async_cache_write(collection, key, blob, timeout).connect(std::bind(&elliptics_service_t::on_write_completed,
		promise, _1, _2));

	return promise;
}

deferred<std::map<std::string, std::string> > elliptics_service_t::bulk_read(const std::string &collection, const std::vector<std::string> &keys)
{
	deferred<std::map<std::string, std::string> > promise;

	auto result = m_elliptics->async_bulk_read(collection, keys);
	result.first.connect(std::bind(&elliptics_service_t::on_bulk_read_completed,
		promise, std::move(result.second), _1, _2));

	return promise;
}

deferred<std::map<std::string, int> > elliptics_service_t::bulk_write(const std::string &collection, const std::vector<std::string> &keys,
	const std::vector<std::string> &blobs)
{
	(void) collection;
	(void) keys;
	(void) blobs;

	deferred<std::map<std::string, int> > promise;

	promise.abort(ENOTSUP, "Not supported yet");

	return promise;
}

void elliptics_service_t::on_read_completed(deferred<std::string> promise,
	const ioremap::elliptics::sync_read_result &result,
	const ioremap::elliptics::error_info &error)
{
	if (error) {
		promise.abort(-error.code(), error.message());
	} else {
		promise.write(result[0].file().to_string());
	}
}

void elliptics_service_t::on_write_completed(deferred<void> promise,
	const ioremap::elliptics::sync_write_result &,
	const ioremap::elliptics::error_info &error)
{
	if (error) {
		promise.abort(-error.code(), error.message());
	} else {
		promise.close();
	}
}

void elliptics_service_t::on_find_completed(deferred<std::vector<std::string> > promise,
	const ioremap::elliptics::sync_find_indexes_result &result,
	const ioremap::elliptics::error_info &error)
{
	if (error) {
		promise.abort(-error.code(), error.message());
	} else {
		promise.write(storage::elliptics_storage_t::convert_list_result(result));
	}
}

void elliptics_service_t::on_remove_completed(deferred<void> promise,
	const ioremap::elliptics::sync_remove_result &,
	const ioremap::elliptics::error_info &error)
{
	if (error) {
		promise.abort(-error.code(), error.message());
	} else {
		promise.close();
	}
}

void elliptics_service_t::on_bulk_read_completed(deferred<std::map<std::string, std::string> > promise,
	const key_name_map &keys,
	const ioremap::elliptics::sync_read_result &result,
	const ioremap::elliptics::error_info &error)
{
	if (error) {
		promise.abort(-error.code(), error.message());
	} else {
		std::map<std::string, std::string> read_result;

		for (size_t i = 0; i < result.size(); ++i) {
			const auto &entry = result[i];
			const auto &id = reinterpret_cast<const dnet_raw_id &>(entry.command()->id);

			auto it = keys.find(id);

			if (it == keys.end()) {
				continue;
			}

			read_result[it->second] = entry.file().to_string();
		}

		promise.write(read_result);
	}
}

// Not implemented yet
void elliptics_service_t::on_bulk_write_completed(deferred<std::map<std::string, int> > promise,
	const key_name_map &keys,
	const ioremap::elliptics::sync_write_result &result,
	const ioremap::elliptics::error_info &error)
{
	(void) promise;
	(void) keys;
	(void) result;
	(void) error;
}

}
